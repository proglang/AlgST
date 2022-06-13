{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

module AlgST.CommandLine
  ( getOptions,
    RunOpts (..),
    Source (..),
    Action (..),
    actionSource,
  )
where

import AlgST.Interpret qualified as I
import AlgST.Util.Output
import Control.Applicative
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Numeric.Natural (Natural)
import Options.Applicative qualified as O

data Source
  = SourceFile !FilePath
  | SourceMain
  | SourceStdin
  deriving (Eq, Show)

sourceParser :: O.Parser Source
sourceParser =
  fmap decideInput . O.optional . O.strArgument . mconcat $
    [ O.metavar "FILE",
      O.help
        "Read Main module from FILE. Use ‘-’ to read from standard input. \
        \Omitting FILE searches for the Main module in the search path."
    ]
  where
    decideInput (Just "-") = SourceStdin
    decideInput (Just fp) = SourceFile fp
    decideInput Nothing = SourceMain

data Action
  = ActionTySynth !String
  | ActionKiSynth !String
  | ActionNF !String
  deriving (Show)

actionSource :: Action -> String
actionSource = \case
  ActionTySynth s -> s
  ActionKiSynth s -> s
  ActionNF s -> s

actionParser :: O.Parser Action
actionParser = tysynth <|> kisynth <|> nf
  where
    synthHelp x y =
      unwords
        [ "Synthesize the",
          x,
          "of the given",
          y,
          "in the context of the Main module.",
          "Can be repeated."
        ]
    tysynth =
      fmap ActionTySynth . O.strOption . mconcat $
        [ O.long "type",
          O.short 'T',
          O.metavar "EXPR",
          O.help $ synthHelp "type" "expression"
        ]
    kisynth =
      fmap ActionKiSynth . O.strOption . mconcat $
        [ O.long "kind",
          O.short 'K',
          O.metavar "TYPE",
          O.help $ synthHelp "kind" "type"
        ]
    nf =
      fmap ActionNF . O.strOption . mconcat $
        [ O.long "nf",
          O.metavar "TYPE",
          O.help
            "Calculate the normal form of the given type in the context of \
            \the Main module. Can be repeated."
        ]

data RunOpts = RunOpts
  { optsSource :: !Source,
    optsOutputMode :: !(Maybe OutputMode),
    optsActions :: ![Action],
    optsDebugEval :: !Bool,
    optsBufferSize :: !Natural,
    optsDriverPaths :: !(Seq FilePath),
    optsDriverSeq :: !Bool,
    optsDriverDeps :: !Bool,
    optsDriverModSearch :: !Bool
  }
  deriving (Show)

optsParser :: O.Parser RunOpts
optsParser = do
  optsSource <- sourceParser
  optsDriverPaths <- driverSearchDirs
  optsActions <- many actionParser
  optsOutputMode <- optional modeParser
  optsBufferSize <- evalBufSizeParser
  optsDebugEval <- evalVerboseParser
  optsDriverSeq <- driverSeqParser
  optsDriverDeps <- driverDepsParser
  optsDriverModSearch <- driverModSearchParser
  pure RunOpts {..}

modeParser :: O.Parser OutputMode
modeParser = plain <|> colorized
  where
    plain =
      O.flag' Plain $
        mconcat
          [ O.long "plain",
            O.short 'p',
            O.help "Output messages without colors.",
            O.hidden
          ]
    colorized =
      O.flag' Colorized $
        mconcat
          [ O.long "colors",
            O.help
              "Output messages with colors even when the output device is \
              \not a terminal.",
            O.hidden
          ]

evalVerboseParser :: O.Parser Bool
evalVerboseParser =
  O.flag False True $
    mconcat
      [ O.long "eval-verbose",
        O.help "Output verbose messages during evaluation.",
        O.hidden
      ]

evalBufSizeParser :: O.Parser Natural
evalBufSizeParser =
  O.option O.auto . mconcat $
    [ O.long "eval-chan-size",
      O.value (I.evalBufferSize I.defaultSettings),
      O.metavar "N",
      O.help
        "The buffer size of channels when interpreted. ‘0’ specifies fully \
        \synchronous communication.",
      O.showDefault,
      O.hidden
    ]

driverSearchDirs :: O.Parser (Seq FilePath)
driverSearchDirs =
  fmap nullDefault . O.many . O.strOption . mconcat $
    [ O.long "search-dir",
      O.short 'I',
      O.metavar "DIR",
      O.help
        "Search the given directory for imported modules. Can be repeated to \
        \search multiple directories in order. If not specfied it defaults to \
        \the working directory."
    ]
  where
    nullDefault [] = Seq.singleton "."
    nullDefault ps = Seq.fromList ps

driverSeqParser :: O.Parser Bool
driverSeqParser =
  driverDebugFlag
    "driver-sequential"
    "Disable concurrency in the driver."

driverDepsParser :: O.Parser Bool
driverDepsParser =
  driverDebugFlag
    "driver-verbose-deps"
    "Enable verbose output during dependency discover, and print the \
    \resulting dependency graph."

driverModSearchParser :: O.Parser Bool
driverModSearchParser =
  driverDebugFlag
    "driver-verbose-modules"
    "Enable verbose output regarding which modules are searched for, where \
    \they are found or why they are not found."

driverDebugFlag :: String -> String -> O.Parser Bool
driverDebugFlag name help =
  O.flag False True $
    O.long name <> O.help help <> O.hidden

getOptions :: IO RunOpts
getOptions =
  O.execParser $
    O.info
      (optsParser <**> O.helper)
      (mconcat parserInfo)
  where
    parserInfo =
      [ O.header
          "AlgST - frontend, typechecker and interpreter for Algebraic \
          \Session Types."
      ]

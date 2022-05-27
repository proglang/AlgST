{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

module AlgST.CommandLine
  ( getOptions,
    RunOpts (..),
    Source (..),
    sourceIsFile,
    sourceIsTerm,
    sourcePrettyName,
    readSource,
    Action (..),
    actionSource,
  )
where

import AlgST.Interpret qualified as I
import AlgST.Util.Output
import Control.Applicative
import Numeric.Natural (Natural)
import Options.Applicative qualified as O
import System.FilePath
import System.IO

data Source
  = SourceFile !FilePath
  | SourceStdin
  deriving (Show)

sourcePrettyName :: Source -> Maybe String
sourcePrettyName = \case
  SourceFile fp -> Just (normalise fp)
  SourceStdin -> Nothing

sourceIsFile :: Source -> Bool
sourceIsFile = \case
  SourceFile _ -> True
  _ -> False

sourceIsTerm :: Source -> Bool
sourceIsTerm = \case
  SourceStdin -> True
  _ -> False

readSource :: Source -> IO String
readSource = \case
  -- When reading from STDIN we wait for all the input to avoid the case where
  -- messages may overlap with the input prompt.
  SourceStdin -> getContents'
  SourceFile fp -> readFile fp

sourceParser :: O.Parser Source
sourceParser =
  fmap (maybe SourceStdin SourceFile)
    . O.optional
    . O.strArgument
    $ mconcat [O.metavar "FILE", O.help fpHelp]
  where
    fpHelp =
      "If a FILE is given input will be read from this file. Otherwise it \
      \will be read from STDIN."

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
          "for the given",
          y,
          "in the context of the parsed program.",
          "May be repeated."
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
          O.help "Calculate the normal form of the given type. May be repeated."
        ]

data RunOpts = RunOpts
  { optsSource :: !Source,
    optsOutputMode :: !(Maybe OutputMode),
    optsActions :: ![Action],
    optsDebugEval :: !Bool,
    optsBufferSize :: !Natural,
    optsDriverSeq :: !Bool,
    optsDriverDeps :: !Bool,
    optsDriverModSearch :: !Bool
  }
  deriving (Show)

optsParser :: O.Parser RunOpts
optsParser = do
  optsOutputMode <- optional modeParser
  optsSource <- sourceParser
  optsActions <- many actionParser
  optsBufferSize <- bufSizeParser
  optsDebugEval <- debugParser
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
            O.help "Output messages without colors."
          ]
    colorized =
      O.flag' Colorized $
        mconcat
          [ O.long "colors",
            O.help
              "Output messages with colors even when the output device is \
              \not a terminal."
          ]

debugParser :: O.Parser Bool
debugParser =
  O.flag False True $
    mconcat
      [ O.long "debug",
        O.short 'd',
        O.help "Output debug messages during evaluation."
      ]

bufSizeParser :: O.Parser Natural
bufSizeParser =
  O.option O.auto . mconcat $
    [ O.long "buffer-size",
      O.short 'B',
      O.value (I.evalBufferSize I.defaultSettings),
      O.help
        "The buffer size of channels when interpreted. ‘0’ specifies fully \
        \synchronous communication.",
      O.showDefault,
      O.hidden
    ]

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
getOptions = O.execParser $ O.info (optsParser <**> O.helper) mempty

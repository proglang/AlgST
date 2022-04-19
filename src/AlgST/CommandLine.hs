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

import AlgST.Util.Output
import Control.Applicative
import Options.Applicative qualified as O
import System.FilePath

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
  SourceStdin -> getContents
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
    optsDebugEval :: !Bool
  }
  deriving (Show)

optsParser :: O.Parser RunOpts
optsParser = do
  optsOutputMode <- optional modeParser
  optsSource <- sourceParser
  optsActions <- many actionParser
  optsDebugEval <- debugParser
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

getOptions :: IO RunOpts
getOptions = O.execParser $ O.info (optsParser <**> O.helper) mempty

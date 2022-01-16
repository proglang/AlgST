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
import qualified Options.Applicative as O
import System.FilePath

data Source
  = SourceFile !FilePath
  | SourceLiteral !String
  | SourceStdin
  deriving (Show)

sourcePrettyName :: Source -> Maybe String
sourcePrettyName = \case
  SourceFile fp -> Just (normalise fp)
  SourceLiteral _ -> Nothing
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
  SourceLiteral s -> pure s

-- No arguments: STDIN
-- One argument: FILE       (can be forced with --file)
-- 1+ arguments: error
--
-- One argument + --file: FILE
-- 1+ arguments + --src: LITERAL
sourceParser :: O.Parser Source
sourceParser = sourceFile <|> sourceLiteral <|> sourceImplicit
  where
    sourceFile =
      let flagOpts =
            mconcat
              [ O.long "file",
                O.help "Read source from given path."
              ]
       in O.flag' SourceFile flagOpts <*> O.strArgument fpOpts
    sourceLiteral =
      let flagOpts =
            mconcat
              [ O.long "src",
                O.help
                  "Interpret arguments as literal AlgST source. Multiple \
                  \arguments are joined by newlines."
              ]
          argOpts = O.metavar "SOURCE"
       in O.flag' (SourceLiteral . unlines) flagOpts <*> some (O.strArgument argOpts)
    sourceImplicit =
      fmap (maybe SourceStdin SourceFile)
        . O.optional
        . O.strArgument
        $ fpOpts <> O.help fpHelp
    fpOpts =
      mconcat [O.metavar "FILE"]
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
    optsActions :: ![Action]
  }
  deriving (Show)

optsParser :: O.Parser RunOpts
optsParser = do
  optsOutputMode <- optional modeParser
  optsSource <- sourceParser
  optsActions <- many actionParser
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

getOptions :: IO RunOpts
getOptions = O.execParser $ O.info (optsParser <**> O.helper) mempty

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
  )
where

import AlgST.Util.Output
import Control.Applicative
import Data.Foldable
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

data RunOpts = RunOpts
  { optsSource :: !Source,
    optsOutputMode :: !(Maybe OutputMode),
    optsQuiet :: !Bool
  }
  deriving (Show)

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

optsParser :: O.Parser RunOpts
optsParser = do
  optsOutputMode <-
    optional $
      asum
        [ O.flag' Plain $
            mconcat
              [ O.long "plain",
                O.short 'p',
                O.help "Output messages without colors."
              ],
          O.flag' Colorized $
            mconcat
              [ O.long "colors",
                O.help
                  "Output messages with colors even when the output device is \
                  \not a terminal."
              ]
        ]

  optsQuiet <-
    O.flag False True . mconcat $
      [ O.long "quiet",
        O.short 'q',
        O.help "Suppress status messages."
      ]

  optsSource <-
    sourceParser

  pure RunOpts {..}

getOptions :: IO RunOpts
getOptions = O.execParser $ O.info (optsParser <**> O.helper) mempty

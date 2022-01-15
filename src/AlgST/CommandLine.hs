{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

module AlgST.CommandLine
  ( RunOpts (..),
    getOptions,
  )
where

import AlgST.Util.Output
import Control.Applicative
import Data.Foldable
import qualified Options.Applicative as O

data RunOpts = RunOpts
  { optsSourceFile :: !(Maybe FilePath),
    optsOutputMode :: !(Maybe OutputMode)
  }
  deriving (Show)

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

  optsSourceFile <-
    optional
      . O.strArgument
      $ mconcat
        [ O.metavar "FILE",
          O.help "Source file, reads from STDIN if not provided."
        ]

  pure RunOpts {..}

getOptions :: IO RunOpts
getOptions = O.execParser $ O.info (optsParser <**> O.helper) mempty

module AlgST.Util.Output where

import System.Console.ANSI
import System.IO (Handle)

data OutputMode
  = Colorized
  | Plain
  deriving (Show, Eq)

discoverMode :: Handle -> IO OutputMode
discoverMode h = do
  color <- hSupportsANSIColor h
  pure if color then Colorized else Plain

style :: [SGR] -> ShowS -> ShowS
style [] s = s
style sgr s = showString (setSGRCode sgr) . s . showString (setSGRCode [])

styleBold :: ShowS -> ShowS
styleBold = style [SetConsoleIntensity BoldIntensity]

styleFG :: Color -> ShowS -> ShowS
styleFG color = style [SetColor Foreground Dull color]

applyStyle :: OutputMode -> (a -> a) -> a -> a
applyStyle Colorized f = f
applyStyle Plain _ = id

redFGStyling :: [SGR]
redFGStyling = [SetColor Foreground Dull Red]

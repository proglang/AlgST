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

boldSGR :: SGR
boldSGR = SetConsoleIntensity BoldIntensity

styleBold :: ShowS -> ShowS
styleBold = style [boldSGR]

styleRed :: ShowS -> ShowS
styleRed = style [SetColor Foreground Dull Red]

applyStyle :: OutputMode -> (a -> a) -> a -> a
applyStyle Colorized f = f
applyStyle Plain _ = id

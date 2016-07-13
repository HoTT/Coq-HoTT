#! /usr/bin/env runhaskell
{-# LANGUAGE UnicodeSyntax, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Graph.Inductive
  (reachable, delEdge, mkGraph, nmap, Edge, Gr, DynGraph, UEdge, LEdge, efilter, LNode, labNodes, Graph, delNodes)
import Data.GraphViz
  (Attributes, toGraphID, color, toLabel, printDotGraph, nonClusteredParams, graphToDot, fmtNode, setID, X11Color(..))
import Data.GraphViz.Attributes.Complete
  (Attribute(URL))
import Data.Text.Lazy (Text, pack, unpack)
import Data.List (nub, elemIndex, isSuffixOf, isPrefixOf)
import Control.Monad (liftM2)
import Data.Maybe
import System.Environment
import System.Exit
import System.IO
import System.Console.GetOpt
import Prelude hiding ((.))

(.) :: Functor f ⇒ (a → b) → (f a → f b)
(.) = fmap

dropBack :: Int → [a] → [a]
dropBack n = reverse . drop n . reverse

uedge :: LEdge a → Edge
uedge (x, y, _) = (x, y)

nfilter :: Graph gr ⇒ (LNode a → Bool) → gr a b → gr a b
nfilter p g = delNodes (map fst $ filter (not . p) $ labNodes g) g

untransitive :: DynGraph gr ⇒ gr a b → gr a b
untransitive g = efilter (not . redundant . uedge) g
  where redundant e@(from, to) = to `elem` reachable from (delEdge e g)

read_deps :: String → Gr FilePath ()
read_deps input = mkGraph (zip [0..] nodes) edges
  where
    content :: [(FilePath, FilePath)]
    content = do
      (left, _ : right) ← break (==':') . lines input
      liftM2 (,) (words left) (words right)
    nodes :: [FilePath]
    nodes = nub $ map fst content ++ map snd content
    edges :: [UEdge]
    edges = map (\(from, to) →
      (fromJust $ elemIndex from nodes, fromJust $ elemIndex to nodes, ())) content

cut_dotvo :: String → String
cut_dotvo = dropBack 3

-- strip to basename
basename :: String → String
basename name = if "theories/"          `isPrefixOf` name then drop (length "theories/") name
                else if "coq/theories/" `isPrefixOf` name then "coq/" ++ drop (length "coq/theories/") name
                else name

hottRenameCoqDoc :: String → String
hottRenameCoqDoc p = if "theories/"          `isPrefixOf` p then "HoTT." ++ drop (length "theories/") p
                     else if "coq/theories/" `isPrefixOf` p then "Coq." ++ drop (length "coq/theories/") p
                     else if "contrib/"      `isPrefixOf` p then drop (length "contrib/") p
                     else p

coqDocURL :: String → FilePath → String
coqDocURL base p = base
  ++ map (\c -> if c == '/' then '.' else c) (hottRenameCoqDoc (cut_dotvo p))
  ++ ".html"

label :: Options → FilePath → Attributes
label opts p' =
  [ toLabel (basename $ cut_dotvo p)
  , color myColor
--  , LabelFontColor (X11Color color)
  ] ++ maybe [] (\base -> [URL (pack $ coqDocURL base p)]) (optCoqDocBase opts)
  where
    p = if take 2 p' == "./" then drop 2 p' else p'

    myColor :: X11Color
    myColor
      | "theories/Categories"  `isPrefixOf` p = Magenta
      | "theories/Types"        `isPrefixOf` p = BlueViolet
      | "theories/HIT"          `isPrefixOf` p = Orange
      | "theories/Modalities"   `isPrefixOf` p = Black
      | "contrib/"              `isPrefixOf` p = Cyan4
      | "coq/theories/"         `isPrefixOf` p = Blue
      | "theories/Basics"       `isPrefixOf` p = SaddleBrown
      | "theories/Tactics"     `isPrefixOf` p = Red
--      | "quote/"           `isPrefixOf` p = Gold3
--      | "theory/"          `isPrefixOf` p = BlueViolet
--      | "varieties/"       `isPrefixOf` p = Red
      | otherwise = Green

makeGraph :: Options -> String -> Text
makeGraph opts = printDotGraph .
  setID (toGraphID $ optTitle opts) .
  graphToDot (nonClusteredParams {fmtNode = snd}) .
  nmap (label opts).
  untransitive .
  nfilter (isSuffixOf ".vo" . snd) .
  read_deps

data Options = Options {
  optCoqDocBase :: Maybe String,
  optTitle :: String,
  optInput :: IO String,
  optOutput :: String -> IO ()
}

defaultOptions :: Options
defaultOptions = Options {
  optCoqDocBase = Nothing,
  optTitle = "",
  optInput = getContents,
  optOutput = putStr
}

options :: [OptDescr (Options -> IO Options)]
options = [
  Option [] ["coqdocbase"] (ReqArg (\arg opt ->
    return opt { optCoqDocBase = Just arg }) "URL") "coqdoc base path (include trailing slash)",
  Option ['i'] ["input"] (ReqArg (\arg opt ->
    return opt { optInput = readFile arg }) "FILE") "input file, stdin if omitted",
  Option ['o'] ["output"] (ReqArg (\arg opt ->
    return opt { optOutput = writeFile arg }) "FILE") "output file, stdout if omitted",
  Option ['t'] ["title"] (ReqArg (\arg opt ->
    return opt { optTitle = arg }) "TITLE") "title of the graph page",
  Option ['h'] ["help"] (NoArg (\_ ->
    usage >> exitSuccess)) "display this help page"]

usage :: IO ()
usage = do
  prg <- getProgName
  hPutStrLn stderr $ usageInfo ("Usage: " ++ prg ++" [OPTION...]") options
  hPutStrLn stderr "Use dot -Tsvg deps.dot -o deps.svg to render the graph"
  hPutStrLn stderr $ replicate 30 ' ' ++ "This DepsToDot has Super Coq Powers."

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
   (actions,_,[]) -> do
     opts <- foldl (>>=) (return defaultOptions) actions
     input <- optInput opts
     optOutput opts $ unpack $ makeGraph opts $ input
   (_,_,errors) -> do
     hPutStrLn stderr $ concat errors
     usage
     exitFailure

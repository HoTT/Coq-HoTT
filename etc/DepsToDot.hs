#! /usr/bin/env runhaskell
{-# LANGUAGE UnicodeSyntax, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Graph.Inductive
  (reachable, delEdge, mkGraph, nmap, Edge, Gr, DynGraph, UEdge, LEdge, efilter, LNode, labNodes, Graph, delNodes)
import Data.GraphViz
  (Attribute(..), Label(..), printDotGraph, nonClusteredParams, graphToDot, fmtNode, Color(..), X11Color(..))
import Data.List (nub, elemIndex, isSuffixOf, isPrefixOf)
import Control.Monad (liftM2)
import Data.Maybe
import System
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
basename = drop 1 . dropWhile (/= '/')

coqDocURL :: String → FilePath → String
coqDocURL base p = base
  ++ map (\c -> if c == '/' then '.' else c) (cut_dotvo p)
  ++ ".html"

label :: Options → FilePath → [Attribute]
label opts p =
  [ Label (StrLabel (basename $ cut_dotvo p))
  , Color [X11Color color]
  , LabelFontColor (X11Color color)
  ] ++ maybe [] (\base -> [URL (coqDocURL base p)]) (optCoqDocBase opts)
  where
    color :: X11Color
    color
      | "categories/"      `isPrefixOf` p = Magenta
      | "implementations/" `isPrefixOf` p = Gold3
      | "interfaces/"      `isPrefixOf` p = Green
      | "misc/"            `isPrefixOf` p = Cyan4
      | "orders/"          `isPrefixOf` p = Blue
      | "quote/"           `isPrefixOf` p = Orange
      | "theory/"          `isPrefixOf` p = BlueViolet
      | "varieties/"       `isPrefixOf` p = Red
      | otherwise = Gray

makeGraph :: Options -> String -> String
makeGraph opts = printDotGraph .
  graphToDot (nonClusteredParams {fmtNode = snd}) .
  nmap (label opts).
  untransitive .
  nfilter (isSuffixOf ".vo" . snd) .
  read_deps

data Options = Options {
  optCoqDocBase :: Maybe String,
  optInput :: IO String,
  optOutput :: String -> IO ()
}

defaultOptions :: Options
defaultOptions = Options {
  optCoqDocBase = Nothing,
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
     optOutput opts $ makeGraph opts $ input
   (_,_,errors) -> do
     hPutStrLn stderr $ concat errors
     usage
     exitFailure

\documentclass{beamer}
%
% Choose how your presentation looks.
%
% For more themes, color themes and font themes, see:
% http://deic.uab.es/~iblanes/beamer_gallery/index_by_theme.html
%
\mode<presentation>
{
  \usetheme{default}      % or try Darmstadt, Madrid, Warsaw, ...
  \usecolortheme{default} % or try albatross, beaver, crane, ...
  \usefonttheme{default}  % or try serif, structurebold, ...
  \setbeamertemplate{navigation symbols}{}
  \setbeamertemplate{caption}[numbered]
}
%include lhs2TeX.fmt
%include polycode.fmt

\usepackage[greek, english]{babel}
\usepackage[utf8x]{inputenc}

% Comment the following lines to use the default Computer Modern font
% instead of the Palatino font provided by the mathpazo package.
% Remove the 'osf' bit if you don't like the old style figures.
% \usepackage[T1]{fontenc}
\usepackage{FiraSans}
% \usepackage[sc,osf]{mathpazo}

\usepackage{tikz}
\usepackage{tikz-qtree,tikz-qtree-compat}
\usepackage{tikz-cd}
\usepackage{hyperref}
\usepackage{xcolor}
\usepackage{ulem} % for \sout - striked-out text

\usepackage{minted}
\newenvironment{code}{\VerbatimEnvironment\begin{minted}{haskell}}{\end{minted}}
% Literate code that will not be included in resulting document - i.e. code for ghci only.
\newenvironment{spec}{\VerbatimEnvironment\begin{minted}{haskell}}{\end{minted}}
% semiverbatim is beamer’s feature
% \newenvironment{code}{\begin{semiverbatim}}{\end{semiverbatim}}

\definecolor{dark-red}{rgb}{0.45,0.17,0.17}
\definecolor{url-color}{rgb}{0.4, 0.0, 0.7}

\def\name{Sergey Vinokurov}
\def\titleMacro{Recursion Schemes - Why, How and More}

% The following metadata will show up in the PDF properties
\hypersetup{
  colorlinks  = true,
  pdfauthor   = {\name},
  pdfkeywords = {functional programming, recursion schemes, Haskell},
  pdftitle    = {\titleMacro},
  pdfsubject  = {Curriculum Vitae},
  pdfpagemode = UseNone,
  urlcolor    = {url-color},
  linkcolor   = {url-color}
}

\title{\titleMacro}
\author{\name}
\institute{serg.foo@@gmail.com, @@5ergv}
\date{2017-11-17}

% Let emphasize actually italicize text.
\renewcommand\emph{\textit}

\newcommand\doubleplus{+\kern-1.3ex+\kern0.8ex}
\newcommand\mdoubleplus{\ensuremath{\mathbin{+\mkern-10mu+}}}

\newcommand{\strConc}[2]{\ensuremath{{#1} \mdoubleplus {#2}}}

\newcommand{\vpipe}{||}

\newcommand{\reVar}[1]{\ensuremath{\text{#1}}}
\newcommand{\reSeq}[2]{\ensuremath{{#1} \cdot {#2}}}
\newcommand{\reAlt}[2]{\ensuremath{{#1} \;\vpipe\; {#2}}}
\newcommand{\reRep}[1]{\ensuremath{{#1}^{*}}}
\newcommand{\emptyStr}{\ensuremath{\varepsilon}}
\newcommand{\reEps}{\emptyStr}

\newcommand{\evalArrow}{\ensuremath{\Rightarrow}}

% Create some vertical space
% \newcommand{\verticalSeparator}{\vspace{0.00cm}}
\newcommand{\verticalSeparator}{\hbox{}}

% \newcommand{\boxed}[1]{\text{\fboxsep=.2em\fbox{\m@th$\displaystyle#1$}}}

% For beginners
%format == = "\;{==}\;"
%format || = "\;{||}\;"
%format && = "\;{\&\&}\;"

% For workin \eval{...}
%options ghci -XDeriveFunctor -XDeriveFoldable -XDeriveTraversable -XGADTs -XKindSignatures -XLambdaCase -XPolyKinds -XRankNTypes -XScopedTypeVariables -XStandaloneDeriving -XTypeApplications

% https://wiki.haskell.org/Literate_programming
\long\def\ignore#1{}

\ignore{
\begin{code}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}

import Data.Coerce
import Data.Foldable
import Data.Monoid
\end{code}
}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}

% Uncomment these lines for an automatically generated outline.
\begin{frame}{Outline}
  \tableofcontents
\end{frame}

\section{Introduction}

\begin{frame}{What}

  An FP pattern for \sout{working with ASTs} \emph{writing compilers}\\

  \pause

  Get recursion out - can change it later\\

  \pause

  Let’s go, there’s lot to cover. Ask questions!

\end{frame}

\section{Recursive datatypes 101 - Lists}

\begin{frame}{What’s in a list?}

  List is either empty or an element consed onto another list.

  \verticalSeparator

\begin{code}
-- Recursive datatype!
data List a =
    Nil
  | Cons a (List a)
  deriving (Show)
\end{code}

\end{frame}

\begin{frame}{Processing lists}

\begin{code}
-- Let’s multiply all list elements together.
prodList :: List Double -> Double
prodList Nil         = 1
prodList (Cons x xs) = x * prodList xs
\end{code}

\begin{code}
-- And compute length
lengthList :: List a -> Int
lengthList Nil         = 0
lengthList (Cons _ xs) = 1 + lengthList xs
\end{code}

  Expected output\\
  |prodList   (Cons 1 (Cons 2 (Cons 3 Nil)))| $\evalArrow$ \eval{prodList (Cons 1 (Cons 2 (Cons 3 Nil)))}\\
  |lengthList (Cons 1 (Cons 2 (Cons 3 Nil)))| $\evalArrow$ \eval{lengthList (Cons 1 (Cons 2 (Cons 3 Nil)))}\\

\end{frame}

\begin{frame}{Explicit recursion leaves out without modularity}

  What if we want to fuse |prodList| and |lengthList|?\\

  Why? - Say, we’d like to do only \emph{one} traversal over a list.\\

  \pause

  Can we reuse already written |prodList| and |lengthList|\\

  \pause

\end{frame}

\begin{frame}{Fusing two list functions}

  Let’s see...\\

  Expected output\\
  |computeBoth (Cons 1 (Cons 2 (Cons 3 Nil)))| $\evalArrow$ \eval{computeBoth (Cons 1 (Cons 2 (Cons 3 Nil)))}\\

  \pause

  No way to combine |prodList| and |lengthList|. Each
  function does it’s own traversal and we cannot alter that.

  \pause

\begin{code}
computeBoth :: List Double -> (Int, Double)
computeBoth Nil         = (0, 1)
computeBoth (Cons x xs) =
  let (len, pr) = computeBoth xs in (len + 1, x * pr)
\end{code}

  \pause

  NB Even |foldr| does not help us here (homework: convince yourself that it’s the case).

\end{frame}

\section{Recursive datatypes 102 - taking recursion out}

\begin{frame}{The path forward}

  \emph{Key idea}: split datatypes into recursive and non-recursive part.\\

  Let’s try it with lists. I’ll introduce non-recursive part first.\\

  Just go ahead and replace all recursive occurrences with new parameter.

\begin{code}
-- Base functor that captures the shape of our type.
data ListF a r =
    NilF
  | ConsF a r
  deriving (Show, Functor)
\end{code}

\end{frame}

\begin{frame}{The Base Functor}

  What will happen when we start consing like we did before?
  % Can use this raw functor to specify things like ‘list no longer than 3’.

\begin{spec}
-- Base functor that captures the shape of our type.
data ListF a r =
    NilF
  | ConsF a r
  deriving (Show, Functor)
\end{spec}

  \eval{:t NilF}\\
  \eval{:t ConsF () NilF}\\
  \eval{:t ConsF () (ConsF () NilF)}\\

\end{frame}

\begin{frame}{A way to use base functor for lists}

  Can use this raw functor to specify things like ‘list no longer than 3’.

\begin{spec}
-- Base functor that captures the shape of our type.
data ListF a r =
    NilF
  | ConsF a r
  deriving (Show, Functor)
\end{spec}

\begin{code}
type List3 a = ListF a (ListF a (ListF a ()))

nullList3 :: List3 a -> Bool
nullList3 NilF = True
nullList3 _    = False
\end{code}

\end{frame}

\begin{frame}{We need recursion}

  Still, |List3| is not enough.\\

  We can specify a list of any fixed length, but we cannot nest
  |ListF|’s to get infinitely-long lists - we will get infinite
  type!

\end{frame}

\begin{frame}{The missing recursion bit}

  Let’s define a type that will add recursion to the |ListF|.

\begin{code}
-- Recursive part of our datatype.
-- NB use newtype to avoid extra layers and have the same runtime
-- representation as we had before.
newtype Fix f = Fix (f (Fix f))
\end{code}

\begin{code}
-- Unwrap one layer
unFix :: Fix f -> f (Fix f)
unFix (Fix x) = x
\end{code}

\end{frame}

\begin{frame}{Recovering |List|}

  |Fix (ListF a)| will give us exactly the |List a| we had before!

\begin{spec}
data List a = Nil | Cons a (List a)

newtype Fix f = Fix (f (Fix f))

data ListF a r = NilF | ConsF a r
\end{spec}

\begin{code}
-- Convenient type alias that does the job
type List' a = Fix (ListF a)
\end{code}

\pause

\begin{itemize}
\item |Nil| $\Leftrightarrow$ |Fix NilF|\\
\item |Cons 1 Nil| $\Leftrightarrow$ |Fix (ConsF 1 (Fix NilF))|\\
\item |Cons 1 (Cons 2 Nil)| $\Leftrightarrow$\\
  |Fix (ConsF 1 (Fix (ConsF 2 (Fix NilF))))|
\end{itemize}

\end{frame}

\begin{frame}{How to work with this}

  Great, now we can rewrite |List a| as |Fix (ListF a)|!!\\

  What now??\\

  \pause

  Let’s actually look at recursion schemes.

\end{frame}

\begin{frame}{Our first recursion scheme}

  The most basic recursion scheme bears proud name \emph{catamorphism}.\\

  The name comes from from the Greek: {\greektext κατά} “downwards” and {\greektext μορφή} “form, shape”. (\href{https://en.wikipedia.org/wiki/Catamorphism}{Wikipedia}).\\

  One cool bit is that catamorphism’s definition can be inferred from
  its commutative diagram (how cool is that!).

\end{frame}

\begin{frame}{Catamorphism from a commutative diagram}

  But let’s write function’s type first. We actually want something like this:

\begin{spec}
cata :: (f a -> a) -> Fix f -> a
\end{spec}

  We’ll revise this a bit afer looking at the diagram.\\

  For now just note that first argument is called algebra and that
  catamorphism collapses possibly infinitely many layers with an algebra.

\end{frame}

\begin{frame}{The diagram}

\begin{spec}
cata :: (f a -> a) -> Fix f -> a
\end{spec}

\begin{center}
  \begin{tikzpicture}[ampersand replacement=\&]
    \matrix (m) [matrix of math nodes,row sep=7em,column sep=9em,minimum width=2em]
    {
      {|f (Fix f)|} \& {|f a|} \\
      {|Fix f|}     \& {|a|}   \\
    };
    \path[-stealth]
    (m-2-1) edge [double] node [below] {|cata f|} (m-2-2) ;
  \end{tikzpicture}
\end{center}

\end{frame}

\begin{frame}{The diagram 2}

\begin{spec}
cata :: (f a -> a) -> Fix f -> a
\end{spec}

\begin{center}
  \begin{tikzpicture}[ampersand replacement=\&]
    \matrix (m) [matrix of math nodes,row sep=7em,column sep=9em,minimum width=2em]
    {
      {|f (Fix f)|} \& {|f a|} \\
      {|Fix f|}     \& {|a|}   \\
    };
    \path[-stealth]
    (m-2-1) edge [double] node [below] {|cata f|} (m-2-2) ;
    \path[-stealth]
    (m-2-1) edge node [left]  {|unFix|} (m-1-1) ;
  \end{tikzpicture}
\end{center}

\end{frame}

\begin{frame}{The diagram 3}

\begin{spec}
cata :: (f a -> a) -> Fix f -> a
\end{spec}

\begin{center}
  \begin{tikzpicture}[ampersand replacement=\&]
    \matrix (m) [matrix of math nodes,row sep=7em,column sep=9em,minimum width=2em]
    {
      {|f (Fix f)|} \& {|f a|} \\
      {|Fix f|}     \& {|a|}   \\
    };
    \path[-stealth]
    (m-2-1) edge [double] node [below] {|cata f|} (m-2-2) ;
    \path[-stealth]
    (m-2-1) edge node [left]  {|unFix|} (m-1-1) ;
    \path[-stealth]
    (m-1-2) edge node [right]  {|f|} (m-2-2) ;
  \end{tikzpicture}
\end{center}

\end{frame}

\begin{frame}{The complete diagram}

%{
%format lookHere = "\begin{alertenv}" Functor " f => \end{alertenv}"
\begin{spec}
fmap :: Functor f => (a -> b) -> f a -> f b

cata :: lookHere (f a -> a) -> Fix f -> a
\end{spec}
%}

\begin{center}
  \begin{tikzpicture}[ampersand replacement=\&]
    \matrix (m) [matrix of math nodes,row sep=7em,column sep=9em,minimum width=2em]
    {
      {|f (Fix f)|} \& {|f a|} \\
      {|Fix f|}     \& {|a|}   \\
    };
    \path[-stealth]
    (m-2-1) edge [double] node [below] {|cata f|} (m-2-2) ;
    \path[-stealth]
    (m-2-1) edge node [left]  {|unFix|} (m-1-1) ;
    \path[-stealth]
    (m-1-2) edge node [right]  {|f|} (m-2-2) ;
    \path[-stealth]
    (m-1-1) edge node [above]  {|fmap (cata f)|} (m-1-2) ;
  \end{tikzpicture}
\end{center}

\end{frame}

\begin{frame}{Read the diagram into a function}

\begin{code}
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix
\end{code}

\begin{center}
  \begin{tikzpicture}[ampersand replacement=\&]
    \matrix (m) [matrix of math nodes,row sep=7em,column sep=9em,minimum width=2em]
    {
      {|f (Fix f)|} \& {|f a|} \\
      {|Fix f|}     \& {|a|}   \\
    };
    \path[-stealth]
    (m-2-1) edge node [below] {|cata f|} (m-2-2) ;
    \path[-stealth]
    (m-2-1) edge node [left]  {|unFix|} (m-1-1) ;
    \path[-stealth]
    (m-1-2) edge node [right]  {|f|} (m-2-2) ;
    \path[-stealth]
    (m-1-1) edge node [above]  {|fmap (cata f)|} (m-1-2) ;
  \end{tikzpicture}
\end{center}

\end{frame}

\begin{frame}{Let’s compute length with our new tool}

\begin{spec}
cata :: Functor f => (f a -> a) -> Fix f -> a
\end{spec}

%{
%format \ = "\textbackslash{}"
\begin{code}
lenAlg :: ListF a Int -> Int
lenAlg = \case
  NilF      -> 0
  ConsF _ x -> x + 1

lengthListF :: List' a -> Int
lengthListF = cata lenAlg
\end{code}
%}

  Run it\\
  |lengthListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))|\\
  $\evalArrow$ \eval{lengthListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))}\\

\end{frame}

\begin{frame}{Let’s compute product with our new tool}

\begin{spec}
cata :: Functor f => (f a -> a) -> Fix f -> a
\end{spec}

%{
%format \ = "\textbackslash{}"
\begin{code}
prodAlg :: ListF Double Double -> Double
prodAlg = \case
  NilF      -> 1
  ConsF x y -> x * y

prodListF :: List' Double -> Double
prodListF = cata prodAlg
\end{code}
%}

  Run it\\
  |prodListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))|\\
  $\evalArrow$ \eval{prodListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))}\\

\end{frame}

\begin{frame}{On to fusion}

\begin{spec}
cata :: Functor f => (f a -> a) -> Fix f -> a
fmap :: Functor f => (a -> b) -> f a -> f b
fst  :: (a, b) -> a
snd  :: (a, b) -> b
\end{spec}

%{
%format \ = "\textbackslash{}"
\begin{code}
fuseAlgs
  :: Functor f
  => (f a -> a)
  ->  (f b -> b)
  ->  (f (a, b) -> (a, b))
fuseAlgs f g = \x -> (f (fmap fst x), g (fmap snd x))

lenWithProdListF :: List' Double -> (Int, Double)
lenWithProdListF = cata (fuseAlgs lenAlg prodAlg)
\end{code}
%}

  \pause

  |lenWithProdListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))|\\
  $\evalArrow$ \eval{lenWithProdListF (Fix (ConsF 3 (Fix (ConsF 4 (Fix NilF)))))}\\

\end{frame}

\section{On to compilers}

\begin{frame}{Compiler datatypes}

  Compilers work with \emph{abstract syntax trees}.\\

  We need a simple tree type for illustration purposes.\\

  \pause
  \verticalSeparator

  Hutton’s Razor - very simple AST to try ideas on.

\begin{code}
data HuttonExpr =
    Lit Double
  | Add HuttonExpr HuttonExpr
\end{code}

\end{frame}

\begin{frame}{Compiler datatypes from a visual standpoint}

  Trees branch, lists are linear.

  \begin{flushleft}
    |Cons 1 (Cons 2 (Cons 3 Nil))|
  \end{flushleft}

  \vspace{-10mm}

  \begin{figure}
    \tikzset{every picture/.style={baseline=(current bounding box.north)}}
    \begin{minipage}[t]{0.48\textwidth}
      \centering
      \begin{tikzpicture}
        \Tree [.Cons \node{1}; [.Cons \node{2}; [.Cons \node{3}; [.Nil ] ] ] ]
      \end{tikzpicture}
    \end{minipage}%
    %
    \begin{minipage}[t]{0.48\textwidth}
      \centering
      \begin{tikzpicture}
        \Tree [.Add [.Add [.Lit \node{5}; ] [.Add [.Lit \node{2}; ] [.Lit \node{3}; ] ] ] [.Lit \node{7}; ] ]
      \end{tikzpicture}
    \end{minipage}
  \end{figure}

  \begin{flushright}
    |Add (Add (Lit 5) (Add (Lit 2) (Lit 3))) (Lit 7)|
  \end{flushright}

\end{frame}

\begin{frame}{What we do with expressions - Evaluate}

  Let’s evaluate |HuttonExpr|

\begin{code}
evalHutton :: HuttonExpr -> Double
evalHutton (Lit n)   = n
evalHutton (Add x y) = evalHutton x + evalHutton y
\end{code}

  \pause
  \verticalSeparator

  Run it\\
  |evalHutton (Add (Add (Lit 5) (Add (Lit 2) (Lit 3))) (Lit 7))|\\
  $\evalArrow$ \eval{evalHutton (Add (Add (Lit 5) (Add (Lit 2) (Lit 3))) (Lit 7))}

  \pause
  % \verticalSeparator
  %
  % All issues that plagued |prodList| and |lengthList| will
  % show up here as well. Now we’re going to fix them.

\end{frame}

\begin{frame}{What we do with expressions - Compute height}

  Say, we want to place all arguments on a stack when generating code.\\

  We’d like to know the maximum depth of the stack we’ll need...

\begin{code}
depthHutton :: HuttonExpr -> Int
depthHutton (Lit _)   = 1
depthHutton (Add x y) =
  1 + (depthHutton x `max` depthHutton y)
\end{code}

  \pause
  \verticalSeparator

  Run it\\
  |depthHutton (Add (Add (Lit 5) (Add (Lit 2) (Lit 3))) (Lit 7))|\\
  $\evalArrow$ \eval{depthHutton (Add (Add (Lit 5) (Add (Lit 2) (Lit 3))) (Lit 7))}

\end{frame}

\begin{frame}{Unfix the |HuttonExpr|}

  All issues that plagued |prodList| and |lengthList| will
  show up with |evalHutton| and |depthHutton| as well. Let’s fix them

\begin{code}
data HuttonExprF r =
    LitF Double
  | AddF r r
  deriving (Show, Functor, Foldable)

type HuttonExpr' = Fix HuttonExprF
\end{code}

\end{frame}

\begin{frame}{Redefine our functions}

\begin{spec}
data HuttonExprF r =
    LitF Double
  | AddF r r
  deriving (Show, Functor, Foldable)
\end{spec}

%{
%format \ = "\textbackslash{}"
\begin{code}
depthAlg :: HuttonExprF Int -> Int
depthAlg = \case
  LitF _   -> 1
  AddF x y -> 1 + (x `max` y)
\end{code}

\pause
\end{frame}

\begin{frame}{Monoids simplify algebras a lot}

\begin{spec}
fold :: (Foldable f, Monoid a) => f a -> a
\end{spec}

\begin{code}
newtype SumMonoid = SumMonoid Double deriving (Show)

instance Monoid SumMonoid where
  mempty  = SumMonoid 0
  mappend = coerce ((+) @Double)

evalAlg :: HuttonExprF SumMonoid -> SumMonoid
evalAlg = \case
  LitF x -> SumMonoid x
  e      -> fold e
\end{code}
%}

\end{frame}

\begin{frame}{Can fuse those with function we defined before}

%{
%format \ = "\textbackslash{}"
\begin{spec}
fuseAlgs
  :: Functor f
  => (f a -> a)
  ->  (f b -> b)
  ->  (f (a, b) -> (a, b))
fuseAlgs f g = \x -> (f (fmap fst x), g (fmap snd x))
\end{spec}

\begin{code}
evalWithDepth :: HuttonExpr' -> (Double, Int)
evalWithDepth = coerce (cata (fuseAlgs evalAlg depthAlg))
\end{code}
%}

\begin{verbatim}
evalWithDepth
  (Fix (AddF
    (Fix (AddF
      (Fix (LitF 5))
      (Fix (AddF (Fix (LitF 2)) (Fix (LitF 3))))))
    (Fix (LitF 7))))
\end{verbatim}
  $\evalArrow$ \eval{evalWithDepth (Fix (AddF
       (Fix (AddF
         (Fix (LitF 5))
         (Fix (AddF (Fix (LitF 2)) (Fix (LitF 3))))))
       (Fix (LitF 7))))}

\end{frame}

\section{Compilers - annotating expressions}

\begin{frame}{Annotating all nodes with a common value}

  Say, we are parsing our expressions from a file.\\

  Each expression has position that we’d like to keep around.\\

  What do we usually do to add positions to each node?

\begin{spec}
-- Just an example
newtype Line     = Line Int
newtype Column   = Column Int
data    Position = Position String Line Column

-- Try adding annotations here
data HuttonExpr =
    Lit Double
  | Add HuttonExpr HuttonExpr
\end{spec}

\end{frame}

\begin{frame}{How to add position without recursion schemes - simple solution}

  For one, we can just go ahead and annotate each constructor

%{
%format lookHere = "\begin{alertenv}" Position "\end{alertenv}"
\begin{spec}
data Position = ...

data HuttonExpr =
    Lit lookHere Double
  | Add lookHere HuttonExpr HuttonExpr
\end{spec}
%}

\pause
Pro: very simple

\pause
Cons:
\begin{itemize}[<+->]
\item Not really feasible if expression type has nearly \emph{100 constructors} (a real case).
\item When constructing expressions we must \emph{always} some position. This leads to lots of meaningless positions
\end{itemize}

\end{frame}

\begin{frame}{How to add position without recursion schemes - smarter solution}

  Okay, we can factor out common field

%{
%format lookHere = "\begin{alertenv}" Position "\end{alertenv}"
\begin{spec}
data Position = ...

data HuttonExpr = HuttonExpr lookHere HuttonExprBase

data HuttonExprBase =
    Lit Double
  | Add HuttonExpr HuttonExpr
\end{spec}
%}

\pause
Pro: still pretty simple

\pause
Cons:
\begin{itemize}[<+->]
\item Now data type is less convenient to work with - try matching 2 or 3 levels deep in a function
\item Still lots of dummy positions when constructing expressions
\end{itemize}

\end{frame}

\begin{frame}{A solution through factored recursion}

  This is where |Cofree| comes in. Compare against |Fix|.\\

  That’s the cofree comonad you might’ve heard of. It’s also helpful
  without |Comonad| instance.

\begin{spec}
newtype Fix f = Fix (f (Fix f))
\end{spec}

\begin{code}
data Cofree f a = a :< f (Cofree f a)
  deriving (Show, Functor, Foldable)
\end{code}

%{
%format lookHere = "\begin{alertenv}" Position "\end{alertenv}"
\begin{spec}
data HuttonExprF r =
    LitF Double
  | AddF r r
  deriving (Show, Functor, Foldable)

type AnnotatedHuttonExpr = Cofree HuttonExprF Position
\end{spec}
%}

\pause
Pro: can ignore all positions and get |Fix|’ed |HuttonExprF|

\pause
Cons: requires unfixed type

\end{frame}

\section{Compilers - adding variables}

\begin{frame}{On to functions}

  We want to model functions with our |HuttonExpr|.\\

  Functions have arguments. Functions of 1 argument with currying will be enough\\

  Quiz: where to put variables if we had old |HuttonExpr|?\\

\begin{spec}
-- If you thought annotations were easy, try adding variables here!!
data HuttonExpr =
    Lit Double
  | Add HuttonExpr HuttonExpr
\end{spec}

\pause

There’s simply no place to do this! We \emph{have} to add new costructor and
rewrite all our functions to handle it.

\end{frame}

\begin{frame}{Variables - add new costructor}

\begin{spec}
data HuttonExprVars a =
    Lit Double
  | Add HuttonExpr HuttonExpr
  | Var a
\end{spec}

This is actually pretty good.\\

Via clever introduction of the new parameter, we can recover old
expressions without variables by using |Void|, a type without
costructors.

\begin{spec}
-- No constructors, ergo no values
-- (except undefined, but it’s morally correct to forget it)
data Void

type HuttonExpr = HuttonExprVars Void
\end{spec}

\end{frame}

\begin{frame}{Variables - add new costructor 2}

\begin{spec}
data HuttonExprVars a =
    Lit Double
  | Add HuttonExpr HuttonExpr
  | Var a

type HuttonExpr = HuttonExprVars Void
\end{spec}

Pro: may be good enough to get the job done\\

\pause
Cons:
\begin{itemize}[<+->]
\item Used a parameter - our type may already have a few of those (5 is not a limit in the RealWorld\texttrademark)
\item Pattern match completeness checker will still expect us to handle new |Var| case even when working with |HuttonExprVars Void|
\end{itemize}

\end{frame}

\begin{frame}{Can modularized recursion help us here?}

  Sure it can! Meet |Free| - a categorical\texttrademark dual of |Cofree|.\\

  That’s the free monad you might’ve heard of. It’s also helpful
  without |Monad| instance.

\begin{code}
data Free f a =
    Pure a
  | Free (f (Free f a))
  deriving (Functor, Foldable)

newtype DeBruijn = DeBruijn Int

type HuttonExprVars = Free HuttonExprF DeBruijn
\end{code}

\end{frame}

\section{Compilers - adding a \emph{bit more} type safety}

\begin{frame}{More complicated ASTs may have invariants}

  That was fun! However, what if our expr can produce either an
  integer or a bool when evaluated?

\begin{code}
data IntBoolExpr =
    LitInt Int
  | LitBool Bool
  | IBAdd IntBoolExpr IntBoolExpr
  | IBLessThan IntBoolExpr IntBoolExpr
  | IBIF
      IntBoolExpr -- must be a bool expr
      IntBoolExpr -- can be any expr
      IntBoolExpr -- can be any expr
\end{code}

\end{frame}

\begin{frame}{Can represent invalid expressions...}

\begin{spec}
data IntBoolExpr =
    LitInt Int
  | LitBool Bool
  | IBAdd IntBoolExpr IntBoolExpr
  | IBLessThan IntBoolExpr IntBoolExpr
  | IBIF
      IntBoolExpr -- must be a bool expr
      IntBoolExpr -- can be any expr
      IntBoolExpr -- can be any expr
\end{spec}

\begin{code}
-- Breaches every invariant we have...
wat :: IntBoolExpr
wat =
  IBIF
    (LitInt 10)
    (LitBool True)
    (IBAdd (LitBool False) (LitInt 1))
\end{code}

\end{frame}

\begin{frame}{Let’s add types so that ill-typed terms will be unrepresentable}

  GADTs to the rescue

\begin{code}
data Expr t where
  ELitInt   :: Int  -> Expr Int
  ELitBool  :: Bool -> Expr Bool
  EAdd      :: Expr Int -> Expr Int -> Expr Int
  ELessThan :: Expr Int -> Expr Int -> Expr Bool
  EIf       :: Expr Bool -> Expr a -> Expr a -> Expr a
\end{code}

\end{frame}

\begin{frame}[fragile]{It works}

Does not compile |EIf (ELitInt 10) (ELitBool True) (EAdd (ELitBool False) (ELitInt 1))|:

\begin{verbatim}
<interactive>:1:6: error:
    * Couldn't match type 'Int' with 'Bool'
      Expected type: Expr Bool
        Actual type: Expr Int
    * In the first argument of 'EIf', namely '(ELitInt 10)'
      In the expression:
        EIf
          (ELitInt 10) (ELitBool True) (EAdd (ELitBool False) (ELitInt 1))

<interactive>:1:35: error:
    * Couldn't match type 'Int' with 'Bool'
      Expected type: Expr Bool
        Actual type: Expr Int
    * In the third argument of 'EIf', namely
        '(EAdd (ELitBool False) (ELitInt 1))'
      In the expression:
        EIf
          (ELitInt 10) (ELitBool True) (EAdd (ELitBool False) (ELitInt 1))

<interactive>:1:41: error:
    * Couldn't match type 'Bool' with 'Int'
      Expected type: Expr Int
        Actual type: Expr Bool
    * In the first argument of 'EAdd', namely '(ELitBool False)'
      In the third argument of 'EIf', namely
        '(EAdd (ELitBool False) (ELitInt 1))'
      In the expression:
        EIf
          (ELitInt 10) (ELitBool True) (EAdd (ELitBool False) (ELitInt 1))
\end{verbatim}

\end{frame}

\begin{frame}{But I want my recursion schemes goodness back!}

  We just need higher-order recursion schemes.\\

  Observe that |Expr| has a type parameter but it is not a |Functor|.
  It’s something different.\\

  Let’s start with a base functor, as before.
\end{frame}

\begin{frame}{Indexed base functor}

  Replace all the recursive positions, add new parameter. The only
  difference: parameter has to be indexed.

\begin{spec}
data ExprF h ix where
  ELitIntF   :: Int  -> ExprF h Int
  ELitBoolF  :: Bool -> ExprF h Bool
  EAddF      :: h Int -> h Int -> ExprF h Int
  ELessThanF :: h Int -> h Int -> ExprF h Bool
  EIfF       :: h Bool -> h a -> h a -> ExprF h a
\end{spec}

\end{frame}

\begin{frame}{Indexed base functor with kind signatures}

  I have just added kind signatures to the parameters

\begin{code}
data ExprF (h :: k -> *) (ix :: k) where
  ELitIntF   :: Int  -> ExprF h Int
  ELitBoolF  :: Bool -> ExprF h Bool
  EAddF      :: h Int -> h Int -> ExprF h Int
  ELessThanF :: h Int -> h Int -> ExprF h Bool
  EIfF       :: h Bool -> h a -> h a -> ExprF h a
\end{code}

\end{frame}

\begin{frame}{Indexed recursion combinator}

  Without further ado, this is how |Fix| should look like for GADTs
  with a parameter (with polykinds):

\begin{code}
-- Just ignore the kinds if they upset your senses...
newtype HFix (f :: (k -> *) -> k -> *) (ix :: k) =
  HFix (f (HFix f) ix)

unHFix :: HFix f ix -> f (HFix f) ix
unHFix (HFix x) = x
\end{code}

\end{frame}

\begin{frame}{We still need functors}

  To define |cata| we needed a |Functor|. Here it’s similar enough -
  our functor should preserve indices:

%{
%format \ = "\textbackslash{}"
\begin{code}
class HFunctor (f :: (k -> *) -> k -> *) where
  hfmap :: (forall ix'. g ix' -> h ix') -> f g ix -> f h ix

-- Can derive with TH, if you like
instance HFunctor ExprF where
  hfmap h = \case
    ELitIntF n     -> ELitIntF n
    ELitBoolF b    -> ELitBoolF b
    EAddF x y      -> EAddF (h x) (h y)
    ELessThanF x y -> ELessThanF (h x) (h y)
    EIfF c t f     -> EIfF (h c) (h t) (h f)
\end{code}
%}

\end{frame}

\begin{frame}{Find 10 differences with |cata|...}

\begin{spec}
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix
\end{spec}

\begin{code}
hcata :: forall f g ix. HFunctor f => (forall ix. f g ix -> g ix) -> HFix f ix -> g ix
hcata alg = go
  where
    go :: forall ix. HFix f ix -> g ix
    go = alg . hfmap go . unHFix
\end{code}

\end{frame}

\begin{frame}{Now we can evaluate safely}

%{
%format \ = "\textbackslash{}"
\begin{code}
data Value ix where
  VInt  :: Int  -> Value Int
  VBool :: Bool -> Value Bool
deriving instance Show (Value ix)

hevalAlg :: ExprF Value ix -> Value ix
hevalAlg = \case
  ELitIntF   n                 -> VInt n
  ELitBoolF  b                 -> VBool b
  EAddF      (VInt x) (VInt y) -> VInt (x + y)
  ELessThanF (VInt x) (VInt y) -> VBool (x < y)
  EIfF       (VBool c) t f     -> if c then t else f

type Expr' = HFix ExprF

heval :: Expr' ix -> Value ix
heval = hcata hevalAlg
\end{code}
%}

\end{frame}

\begin{frame}{Does it actually run??}

  Yes it does!!

\begin{spec}
data Value ix where
  VInt  :: Int  -> Value Int
  VBool :: Bool -> Value Bool

heval :: Expr' ix -> Value ix
\end{spec}

\begin{center}
\line(1,0){250}
\end{center}

\begin{verbatim}
heval
  (HFix (EIfF
    (HFix (ELitBoolF False))
    (HFix (ELitIntF 1))
    (HFix (ELitIntF 42))))
\end{verbatim}
  $\evalArrow$ \eval{heval (HFix (EIfF (HFix (ELitBoolF False)) (HFix (ELitIntF 1)) (HFix (ELitIntF 42))))}

\end{frame}

% ...

% \begin{frame}{Practical use - parallelize traversals!}
%
%   Monads are our friends
%
%   % ps add example
%
% \end{frame}
%
% % ...
%
% \begin{frame}{Practical use - cache traversals!!}
%
%   Monads prove to our friends once again
%
%   % ps add example
%
% \end{frame}

\section{Wrapping up}

\begin{frame}{More recursion schemes}

  I have only scratched the surface. Look:

  \begin{itemize}[<+->]
  \item Folding to a value
    \begin{itemize}[<+->]
    \item Catamorphism - you have learned it in this talk. Well done!
    \item Paramorphism - folding with access to the original expression
    \item Zygomorphism - neat combination of several algebras so that they can use results of each other
    \item Histomorphism - dynamic programming, algebra has access to all previously computed results for a tree
    \end{itemize}
  \item Unfolding from a value
    \begin{itemize}[<+->]
    \item Anamorphism - one level at a time
    \item Futumorphism - multiple levels at a time
    \end{itemize}
  \item Fused
    \begin{itemize}[<+->]
    \item Metamorphism = |ana . cata|
    \item Hylomorphism = |cata . ana|
    \item Dynamorphism = |histo . ana|
    \item Chronomorphism = |futu . histo|
    \end{itemize}
  \item Just a joke
    \begin{itemize}
    \item Zygohistomorphic prepromorphism
    \end{itemize}
  \end{itemize}

  \pause

  Comonads can also help to unify some of those.\\

\end{frame}

\begin{frame}{References}

  Lots of resources. In order of increasing difficulty:

  \begin{itemize}
    \item Bartosz Milewski blog post \href{https://www.schoolofhaskell.com/user/bartosz/understanding-algebras}{“Understanding F-Algebras”}
    \item Tim Williams slides \href{https://github.com/willtim/recursion-schemes/raw/master/slides-final.pdf}{“Recursion Schemes by Example”}
    \item Tim Williams blog post \href{http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html}{“Fixing GADTs”}
    \item Wouter Swierstra \href{http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf}{Data Types \`{a} la Carte}
  \end{itemize}

\end{frame}

\begin{frame}

  \begin{center}
    {\Huge Thank you!}\\
  \end{center}

  \vspace{1cm}
  \pause

  \begin{center}
    {\Huge Questions?}
  \end{center}

\end{frame}

\end{document}

% ----- Configure Emacs -----
%
% Local Variables: ***
% compile-command: "./build.sh" ***
% End: ***

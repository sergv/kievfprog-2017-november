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

\usepackage[english]{babel}
\usepackage[utf8x]{inputenc}

% Comment the following lines to use the default Computer Modern font
% instead of the Palatino font provided by the mathpazo package.
% Remove the 'osf' bit if you don't like the old style figures.
% \usepackage[T1]{fontenc}
\usepackage{FiraSans}
% \usepackage[sc,osf]{mathpazo}

\usepackage{tikz}
\usepackage{tikz-qtree,tikz-qtree-compat}
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
\renewcommand\emph{\it}

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

% Create some vertical space
% \newcommand{\verticalSeparator}{\vspace{0.00cm}}
\newcommand{\verticalSeparator}{\hbox{}}

% \newcommand{\boxed}[1]{\text{\fboxsep=.2em\fbox{\m@th$\displaystyle#1$}}}

% For beginners
%format == = "\;{==}\;"
%format || = "\;{||}\;"
%format && = "\;{\&\&}\;"

% For workin \eval{...}
%options ghci

% \eval{take 10 tms}
\begin{document}

\begin{frame}[fragile]
  \titlepage
\end{frame}

% Uncomment these lines for an automatically generated outline.
\begin{frame}[fragile]{Outline}
 \tableofcontents
\end{frame}

\section{Introduction}

\begin{frame}[fragile]{What}

  \begin{itemize}[<+->]
    \item An FP pattern for \sout{working with ASTs} \emph{writing compilers}
    \item Get recursion out - can change it later
    \item Let’s go, there’s lot to cover. Ask questions!
  \end{itemize}

\end{frame}

% \begin{frame}[fragile]{Motivation}
%
%   \begin{itemize}[<+->]
%     \item This talk is something that becomes common knowledge of compiler writers
%     \item A pattern for working with ASTs
%     \item A pattern for \sout{working with ASTs} \emph{writing compilers}
%     \item Functional programming does have some patterns
%   \end{itemize}
%
% % \vskip 1cm
% %
% % \begin{block}{Examples}
% % Some examples of commonly used commands and features are included, to help you get started.
% % \end{block}
%
% \end{frame}
%
% \begin{frame}[fragile]{Compilers? Huh?}
%
%   At least that’s what I mostly use it for. Is it useful anywhere else?
%
%   \verticalSeparator\pause
%
%   Why, yes! You can
%
%   \begin{itemize}[<+->]
%     \item Understand what code can and cannot do just by looking at which recursion scheme it uses
%     \item Study recursion (rich theory (not in this talk though))
%     \item By separating recursion out we can plug in different scheme that e.g. caches results or parallelizes computations
%   \end{itemize}
%
%   \verticalSeparator\pause
%
%   In other words: more modularity, more separation of concerns
%
% \end{frame}
%
% \begin{frame}[fragile]{Okay, so what is a Recursion Scheme?}
%
%   Let’s handle it slowly. The first word is ‘Recursion’. What does that mean?
%
%   \verticalSeparator\pause
%
%   Yes, there are recursive functions. Factorial! But we are looking a bit further.
%
%   \verticalSeparator
%
%   We want \emph{datatypes}.
%
% \end{frame}

\begin{frame}[fragile]{Okay, so what is a Recursion Scheme?}

  Simple recursive type: a list.

\begin{code}
data List a = Nil | Cons a (List a)
\end{code}

\end{frame}

% ...

\begin{frame}[fragile]{Practical use - parallelize traversals!}

  Monads are our friends

  % ps add example

\end{frame}

% ...

\begin{frame}[fragile]{Practical use - cache traversals!!}

  Monads prove to our friends once again

  % ps add example

\end{frame}


% \section{Regular Expressions refresher}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Definitions}
%
%   Regular Expression are an expression language for describing sets of strings.\\
%   \verticalSeparator\pause
%
%   Strings - sequences of characters. $a, b, c$ - characters, $aaaab, c$ - strings\\
%   \verticalSeparator\pause
%
%   Symbol $\emptyStr$ denotes empty string\\
%   \verticalSeparator\pause
%
%   String concatenation is denoted with $\mdoubleplus$: $\strConc{aaaaaa}{b} = aaaaaab$\\
%
%   \[\forall x: \strConc{x}{\emptyStr} = \strConc{\emptyStr}{x} = x \]\\
%   \verticalSeparator\pause
%
%   Alphabet - set of all characters, denoted $\Sigma$. E.g. $\Sigma = \lbrace a, b, c \rbrace$.\\
%   \verticalSeparator
%
%   % Sample set of strings: $\lbrace b, ab, aab, \ldots, aaaaaaaaab, \ldots \rbrace$\\
%   % \verticalSeparator
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Introducing Haskell ADT for regexps}
%   Regular expressions are defined inductively
%
% \begin{code}
% data Sigma = A | B | C
%   deriving (Show, Eq, Ord, Enum, Bounded)
%
% type Str a = [a]
%
% data Regex a
%   =  Eps                     -- Empty regex
%   |  Sym a                   -- Singleton regex
%   |  Seq (Regex a) (Regex a) -- Sequence
%   |  Alt (Regex a) (Regex a) -- Alternatives
%   |  Rep (Regex a)           -- Repetition
%   deriving (Show, Eq)
% \end{code}
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Example}
%
%   Consider regular expression $\reSeq{\reSeq{\reRep{a}}{b}}{(\reAlt{c}{\reEps})}$
%
%   \pause
%
%   \[L(\reSeq{\reRep{a}}{\reSeq{b}{\reAlt{\reEps}{c}}}) = \lbrace b, bc, ab, abc, aab, aabc, aaab, aaabc, \ldots \rbrace\]
%
%   In Haskell, |re = Seq (Rep (Sym A)) (Seq (Sym B) (Alt Eps (Sym C)))|\\
%
%   \pause
%
%   Or, with less parens |re = Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)|\\
%
%   \pause
%
%   Expected output\\
%   |accept re [B]          =>| \eval{accept (Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)) [B] }\\
%   |accept re [B,C]        =>| \eval{accept (Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)) [B,C] }\\
%   |accept re [A,A,A,B]    =>| \eval{accept (Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)) [A,A,A,B] }\\
%   |accept re [A,A,A,C]    =>| \eval{accept (Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)) [A,A,A,C] }\\
%   |accept re [A,A,A,B,C]  =>| \eval{accept (Rep (Sym A) `Seq` Sym B `Seq` Alt Eps (Sym C)) [A,A,A,B,C] }
% \end{frame}
%
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Defining regexp semantics}
%   For any regex $\reVar(A)$, notation $L(\reVar{A})$ denotes all strings that
%   regex matches.
%
%   Let’s define regexp semantics in Haskell by definning regexp matching function:
% \begin{code}
% accept :: Eq a => Regex a -> Str a -> Bool
% accept Eps        s  = acceptEps s
% accept (Sym c)    s  = acceptSym c s
% accept (Seq x y)  s  = acceptSeq x y s
% accept (Alt x y)  s  = acceptAlt x y s
% accept (Rep x)    s  = acceptRep x s
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Empty string regex}
%   Empty string - $\reEps$ is a regular expression that matches the empty string.
%
%     \[L(\emptyStr) = \lbrace \emptyStr \rbrace\]
%
% \begin{code}
% acceptEps :: Str a -> Bool
% acceptEps s = null s
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Singleton character regex}
%
%   Atoms - all symbols from $\Sigma$ are regular expressions that match themselves.
%
%   \[\forall x \in \Sigma : L(x) = \lbrace x \rbrace\]
%
%   Haskell semantics:
% \begin{code}
% acceptSym :: Eq a => a -> Str a -> Bool
% acceptSym c s = s == [c]
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Concatenation}
%
%   Concatenation - if $\reVar{A}$ and $\reVar{B}$ are regular expressions, so is $\reSeq{\reVar{A}}{\reVar{B}}$
%
%   \[L(\reSeq{\reVar{A}}{\reVar{B}}) = \lbrace \strConc{x}{y}\, \vpipe\, x \in L(\reVar{A}), \, y \in L(\reVar{B}) \rbrace\]
%
%   Haskell semantics:
% \begin{code}
% acceptSeq :: Eq a => Regex a -> Regex a -> Str a -> Bool
% acceptSeq r1 r2 s =
%   or [ accept r1 s1 && accept r2 s2 | (s1, s2) <- split s ]
% \end{code}
%
% \begin{code}
% split :: Str a -> [(Str a, Str a)]
% split xs = map (\(x, y) -> (reverse x, y)) (go [] xs)
%   where
%     go p []      = [(p, [])]
%     go p (c:cs)  = (p, c : cs) : go (c : p) cs
% \end{code}
%
% % Example
% |split "abc" =>| \eval{split "abc"}
%
% \end{frame}
%
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Alternatives}
%
%   Alternative - if $\reVar{A}$ and $\reVar{B}$ are regular expressions, so is $\reAlt{\reVar{A}}{\reVar{B}}$
%
%   \[L(\reAlt{\reVar{A}}{\reVar{B}}) = L(\reVar{A}) \cup L(\reVar{B}) \]
%
%   Haskell semantics:
% \begin{code}
% acceptAlt :: Eq a => Regex a -> Regex a -> Str a -> Bool
% acceptAlt r1 r2 s = accept r1 s || accept r2 s
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Repetition}
%
%   Repetition - also known as Kleene star, if $\reVar{A}$ is a regular expression, so is $\reRep{\reVar{A}}$
%
%   \[L(\reRep{\reVar{A}}) = \lbrace \reEps, \reVar{A}, \reSeq{\reVar{A}}{\reVar{A}}, \reSeq{\reVar{A}}{\reSeq{\reVar{A}}{\reVar{A}}}, \ldots \rbrace \]
%
%   Haskell semantics:
% \begin{code}
% acceptRep :: Eq a => Regex a -> Str a -> Bool
% acceptRep r s = or [ and [ accept r p | p <- ps ] | ps <- parts s ]
% \end{code}
%
% \begin{code}
% parts :: Str a -> [[Str a]]
% parts []      = [[]]
% parts [c]     = [[[c]]]
% parts (c:cs)  =
%   concat [ [(c : p) : ps, [c] : p : ps] | p : ps <- parts cs ]
% \end{code}
%
% % Example
% |parts "abcd" =>| \eval{parts "abcd"}
%
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{What is not a regular expression}
%   \begin{itemize}[<+->]
%     \item Some popular implementations allow “regexps” with backreferences, like $(a\vpipe b\vpipe c)\text{\textbackslash} 1$
%     \item $(.^{*})\text{\textbackslash} 1$ describes non-regular language. Therefore it cannot be converted to finite automaton
%     \item Generally, we want an automaton since it’s very fast
%     \item We don’t include backreferences in our regexps. Regexps without them have enough expressive power
%   \end{itemize}
% \end{frame}
%
% \begin{frame}[fragile]{Regular Expressions refresher}{Drawbacks}
%   \begin{itemize}[<+->]
%     \item Although usefull for defining semantics, |accept| function is not appropriate for practical applications.
%     \item Reliance on function |parts| means exponential worst-case runtime in length of string being matched
%   \end{itemize}
% \end{frame}
%
% \section{Glushkov Automaton Construction}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}
%
%   Glushkov proposed Algorithm for generating Nondeterministic Finite Automaton,
%   NFA, from regular expression.\\
%
%   NFA is a good way to run regexps because
%   \begin{itemize}[<+->]
%     \item Size of NFA is linear in size of regular expression
%     \item Given NFA with $m$ states we can run it on string of $n$ characters in $O(m \cdot n)$ time
%     \item DFA is simpler than NFA but can have $\Omega(2^m)$ states of states for an NFA with $m$ states.
%   \end{itemize}
%
% \end{frame}
%
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example}
%
%   We’re going to fuse translation of regexp to NFA and execution to NFA.
%
%   \pause
%
%   Glushkov observation: every NFA states corresponds to a position within regexp.
%   Position is a place where a symbol occurs.\\
%
%   \pause
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     \begin{tikzpicture}% [level 1/.style={level distance=1.5cm}]
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node{Sym a};
%           \node{Sym b};
%           ]
%         ]
%       [.Seq
%         \node{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
%
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 1}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \pause
%
%   \begin{center}
%     “\fbox{a}babac”
%   \end{center}
%
%   \pause
%
%   \[\reSeq{\reRep{(\reSeq{\fbox{a}}{b})}}{\reSeq{a}{c}}\]
%
%   \pause
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node[draw]{Sym a};
%           \node{Sym b};
%           ]
%         ]
%       [.Seq
%         \node[draw]{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 2}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     “a\fbox{b}abac”
%   \end{center}
%
%   \[\reSeq{\reRep{(\reSeq{a}{\fbox{b}})}}{\reSeq{a}{c}}\]
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node{Sym a};
%           \node[draw]{Sym b};
%           ]
%         ]
%       [.Seq
%         \node{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 3}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     “ab\fbox{a}bac”
%   \end{center}
%
%   \[\reSeq{\reRep{(\reSeq{\fbox{a}}{b})}}{\reSeq{\fbox{a}}{c}}\]
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node[draw]{Sym a};
%           \node{Sym b};
%           ]
%         ]
%       [.Seq
%         \node[draw]{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 4}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     “aba\fbox{b}ac”
%   \end{center}
%
%   \[\reSeq{\reRep{(\reSeq{a}{\fbox{b}})}}{\reSeq{a}{c}}\]
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node{Sym a};
%           \node[draw]{Sym b};
%           ]
%         ]
%       [.Seq
%         \node{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 5}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     “abab\fbox{a}c”
%   \end{center}
%
%   \[\reSeq{\reRep{(\reSeq{\fbox{a}}{b})}}{\reSeq{\fbox{a}}{c}}\]
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node[draw]{Sym a};
%           \node{Sym b};
%           ]
%         ]
%       [.Seq
%         \node[draw]{Sym a};
%         \node{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Example - step 6}
%
%   Let’s match $\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{c}}$ against “ababac”
%
%   \begin{center}
%     “ababa\fbox{c}”
%   \end{center}
%
%   \[\reSeq{\reRep{(\reSeq{a}{b})}}{\reSeq{a}{\fbox{c}}}\]
%
%   \begin{center}
%     \begin{tikzpicture}
%     \Tree
%     [.Seq
%       [.Rep
%         [.Seq
%           \node{Sym a};
%           \node{Sym b};
%           ]
%         ]
%       [.Seq
%         \node{Sym a};
%         \node[draw, red]{Sym c};
%         ]
%     ]
%     \end{tikzpicture}
%   \end{center}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Haskell implementation}
%
% \begin{code}
% data Regex' a
%   =  Eps'                        -- Empty regex
%   |  Sym' Bool a                 -- Singleton regex
%   |  Seq' (Regex' a) (Regex' a)  -- Sequence
%   |  Alt' (Regex' a) (Regex' a)  -- Alternatives
%   |  Rep' (Regex' a)             -- Repetition
%   deriving (Show, Eq)
%
% -- Convenient constructor
% sym' :: a -> Regex' a
% sym' c = Sym' False c
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Moving mark}
%
% \begin{code}
% shift :: Eq a => Bool -> Regex' a -> a -> Regex' a
% shift  _  Eps'          _   =  Eps'
% shift  m  (Sym'  _  c)  c'  =  Sym'  (m && c == c') c
% shift  m  (Alt'  p  q)  c   =  Alt'  (shift m p c)  (shift m q c)
% shift  m  (Seq'  p  q)  c   =
%   Seq' (shift m p c) (shift (m && empty p || final p) q c)
% shift  m  (Rep'  p)     c   = Rep' (shift (m || final p) p c)
% \end{code}
%
% \begin{code}
% empty :: Regex' a -> Bool
% empty  Eps'          =  True
% empty  (Sym'  _  _)  =  False
% empty  (Alt'  p  q)  =  empty p || empty q
% empty  (Seq'  p  q)  =  empty p && empty q
% empty  (Rep'  p)     =  True
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Checking if mark is in the final position}
%
% \begin{code}
% final :: Regex' a -> Bool
% final  Eps'          =  False
% final  (Sym'  m  _)  =  m
% final  (Alt'  p  q)  =  final p || final q
% final  (Seq'  p  q)  =  final p && empty q || final q
% final  (Rep'  p)     =  final p
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Matching}
%
% \begin{code}
% accept' :: Eq a => Regex' a -> [a] -> Bool
% accept' re []        =  empty re
% accept' re (c : cs)  =  final (foldl (shift False) (shift True re c) cs)
% \end{code}
%
%   \pause
%
%   Let’s try our previous test regexp $\reSeq{\reRep{a}}{\reSeq{b}{(\reAlt{\reEps}{c})}}$\\
%
%   |re = Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)|\\
%
%   Expected output\\
%   |accept' re [B]          =>| \eval{accept' (Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)) [B] }\\
%   |accept' re [B,C]        =>| \eval{accept' (Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)) [B,C] }\\
%   |accept' re [A,A,A,B]    =>| \eval{accept' (Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)) [A,A,A,B] }\\
%   |accept' re [A,A,A,C]    =>| \eval{accept' (Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)) [A,A,A,C] }\\
%   |accept' re [A,A,A,B,C]  =>| \eval{accept' (Rep' (sym' A) `Seq'` sym' B `Seq'` Alt' Eps' (sym' C)) [A,A,A,B,C] }
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Improving efficiency}
%
%   It’s costly to recompute |final| and |empty| every time. We can memoize them
%   in expressions
%
% \begin{code}
% data RegexMemo a
%   =  EpsMemo               -- Empty regex
%   |  SymMemo  Bool a       -- Singleton regex
%   |  SeqMemo  (R a) (R a)  -- Sequence
%   |  AltMemo  (R a) (R a)  -- Alternatives
%   |  RepMemo  (R a)        -- Repetition
%   deriving (Show, Eq)
%
% data R a = R
%   { rEmpty  :: Bool
%   , rFinal  :: Bool
%   , rRegex  :: RegexMemo a
%   } deriving (Show, Eq)
% \end{code}
%
% \end{frame}
%
% \begin{frame}[fragile]{Glushkov Automaton Construction}{Improving efficiency}
%
%   Having defined |RegexMemo| and |R|, we can define smart constructors and we’ll
%   only need to replace all explicit constructors with smart constructors in
%   function |shift| to get the benefit.
%
%   E.g.
%
% \begin{code}
% reEps :: R a
% reEps = R
%   { rEmpty  = True
%   , rFinal  = False
%   , rRegex  = EpsMemo
%   }
%
% reAlt :: R a -> R a -> R a
% reAlt p q = R
%   { rEmpty  =  rEmpty p  || rEmpty q
%   , rFinal  =  rFinal p  || rFinal q
%   , rRegex  =  AltMemo p q
%   }
% \end{code}
%
% \end{frame}
%
%
% % \section{Regular expressions as an ADT}
% % \subsection{Straightforward semantics}
% % \subsection{Glushkov Automaton Construction}
% \section{Laziness allows matching strictly more expressive languages}
%
% \begin{frame}[fragile]{One cool laziness trick}
%
%   Laziness allows matching strictly more expressive languages. Even some context-sensitive ones\\
%
%   To make our regex lazy we’ll have to add another field that tracks, whether the
%   expression was active. If it wasn’t, we can avoid forcing it. This would allow
%   us to operate infinte regexps, which can match some context-free languages and
%   even some contex-sensitive ones.\\
%
%   \pause
%
%   Let’s match language of parentheses $\lbrace \emptyStr, (), (()), ()(), (())(), \ldots \rbrace$\\
%
%   Our alphabet is $\Sigma = \lbrace (, ) \rbrace$\\
%
% \begin{code}
% data Parens = LParen | RParen deriving (Show, Eq)
% \end{code}
%
%   Now make regex that matches this language\\
%
%   |let re = (symL LParen `seqL` re `seqL` symL RParen) `seqL` re in re|\\
%
% \end{frame}
%
%
% \begin{frame}[fragile]{One cool laziness trick}{Sample run}
%
%   |let re = (symL LParen `seqL` re `seqL` symL RParen) `seqL` re in re|\\
%
%   \pause
%
%   Try it out
%
%   |acceptLazy re [LParen, RParen]                         => True| % \eval{accept' (let re = (sym' LParen `Seq'` re `Seq'` sym' RParen) `Seq'` re in re) [LParen, RParen] }\\
%   |acceptLazy re [LParen, RParen, LParen, RParen]         => True| % \eval{accept' (let re = (sym' LParen `Seq'` re `Seq'` sym' RParen) `Seq'` re in re) [LParen, RParen, LParen, RParen] }\\
%   |acceptLazy re [LParen, RParen, LParen, RParen, RParen] => False|
%
% \end{frame}

\begin{frame}[fragile]{References}

  Lots of resources. In order of increasing difficulty:

  \begin{itemize}
    \item Bartosz Milewski blog post \href{https://www.schoolofhaskell.com/user/bartosz/understanding-algebras}{“Understanding F-Algebras”}
    \item Tim Williams slides \href{https://github.com/willtim/recursion-schemes/raw/master/slides-final.pdf}{“Recursion Schemes by Example”}
    \item Tim Williams blog post \href{http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html}{“Fixing GADTs”}
  \end{itemize}

% \vskip 1cm
%
% \begin{block}{Examples}
% Some examples of commonly used commands and features are included, to help you get started.
% \end{block}

\end{frame}

\begin{frame}[fragile]

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

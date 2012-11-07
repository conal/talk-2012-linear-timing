% -*- latex -*-
\documentclass{beamer}

% \usetheme{Warsaw} 

\usepackage{beamerthemesplit}

\usepackage{graphicx}
\DeclareGraphicsExtensions{.pdf,.png,.jpg}

\useoutertheme{infolines}

\input{macros}

%include polycode.fmt
%include forall.fmt
%include greek.fmt
%include mine.fmt

% \title{Some fun with linear transformations}
\title{Circuit timing analysis, linear maps, \\and type class morphisms}
\author{Conal Elliott}
\institute{Tabula}
% Abbreviate date/venue to fit in infolines space
\date{IFIP WG 2.8, Nov. 2012}

\begin{document}

\frame{\titlepage}

\nc\ssection[1]{
\section{#1}
\frame{\begin{center}\vspace{3ex}
\LARGE #1\end{center}}
}
% \nc\ssubsection[1]{}
\nc\ssubsection\subsection

\frame{\frametitle{Outline}\tableofcontents}

\ssection{Timing analysis}

\nc\wfig[2]{
\begin{center}
\includegraphics[width=#1]{figures/#2.jpg}
\end{center}
}

\nc\fig[1]{\wfig{3in}{#1}}

\nc\figs[2]{
\begin{center}
\includegraphics[width=1.75in]{figures/#1.jpg}
\hspace{0.5in}
\includegraphics[width=1.75in]{figures/#2.jpg}
\end{center}
}

\nc\wsingle[2]{\wfig{#1}{single/#2}}
\nc\single[1]{\fig{single/#1}}
\nc\singles[2]{\figs{single/#1}{single/#2}}

\frame{\frametitle{Simple timing analysis}
Computation with a time delay:
\single{f}
}

\frame{\frametitle{Trivial timings}
\singles{id}{const}
}

\frame{\frametitle{Sequential composition}
\single{compose}
}

\frame{\frametitle{Parallel composition}
\wsingle{2in}{cross}
}


\frame{\frametitle{But ...}

\singles{cross-oops-A}{cross-oops-B}

Oops: Same circuit (|f *** g|), different timings.

}

\nc\wmulti[2]{\wfig{#1}{multi/#2}}
\nc\multi[1]{\fig{multi/#1}}
\nc\multis[2]{\figs{multi/#1}{multi/#2}}

\frame{\frametitle{Multi-path analysis}
\wmulti{2in}{f}
\begin{itemize}
\item Max delay for \emph{each} input/output pair
\item How do delays \emph{compose}?
\end{itemize}
}

\frame{\frametitle{How do delays \emph{compose}?}
\multi{compose}
}

\frame{\frametitle{How do delays \emph{compose}?}
\wmulti{2in}{compose}

\newcommand{\Max}{\mathop{\mathrm{Max}}}

$V \odot U = W$, where

$$
W_{i,k} = \Max_{j} \; (U_{i,j} + V_{j,k})
$$

\pause
Look familiar? \pause Matrix multiplication?

}

\frame{\frametitle{|MaxPlus| algebra}

> type Delay = MaxPlus Double
> 
> data MaxPlus a = MP a

> instance Ord a => AdditiveGroup (MaxPlus a) where
>   MP a  ^+^ MP b  = MP (a `max` b)
> 
> instance (Ord a, Num a) => VectorSpace (MaxPlus a) where
>   type Scalar (MaxPlus a) = a
>   a  *^ MP b  = MP (a + b)

|VectorSpace| is overkill.
Module over a semi-ring suffices.

\emph{Oops} -- We also need a zero.

}

\frame{\frametitle{|MaxPlus| algebra}

> type Delay = MaxPlus Double
> 
> data MaxPlus a = Minf | Fi a

> instance Ord a => AdditiveGroup (MaxPlus a) where
>   zeroV = Minf
>   MP a  ^+^ MP b  = MP (a `max` b)
>   Minf  ^+^ _     = Minf
>   _     ^+^ Minf  = Minf
> 
> instance (Ord a, Num a) => VectorSpace (MaxPlus a) where
>   type Scalar (MaxPlus a) = a
>   a  *^ MP b  = MP (a + b)
>   _  *^ Minf  = Minf

}

\ssection{Linear transformations}

\frame{\frametitle{Representation?}
How might we represent linear maps/transformations |a :-* b|?

\pause

\begin{itemize}
\item Matrices
\item Functions
\item What else?
\end{itemize}

}

\frame{\frametitle{Matrices}

\nc\one{\mathit{1}}
\begin{itemize}

\item Use a matrix:

$$
\begin{bmatrix} a_{\one \one} & \cdots & a_{\one m} \\ \vdots & \ddots & \vdots \\ a_{n \one} & \cdots & a_{n m} \end{bmatrix}
$$
\item Only handles |Rm :-* Rn| (for ring |R|).
\item Static typing?

\end{itemize}

}

\frame{\frametitle{Statically sized matrices}

> type Mat m n a = Vec m (Vec n a)

> (.) ::  (IsNat m, IsNat o) => 
>         Mat n o D -> Mat m n D -> Mat o m D
> no . mn = crossF dot (transpose no) mn

> crossF ::  (IsNat m, IsNat o) =>
>            (a -> b -> c) -> Vec o a -> Vec m b -> Mat o m c
> crossF f as bs = (\ a -> f a <$> bs) <$> as

> dot ::  (Ord a, Num a) =>
>         Vec n a -> Vec n a -> a
> u `dot` v = sum (zipWithV (*) u v)

}
\frame{\frametitle{Generalizing}

> type Mat m n a = m (n a)

> (.) ::  (Functor m, Applicative n, Traversable n, Applicative o) =>
>         Mat n o D -> Mat m n D -> Mat o m D
> no . mn = crossF dot (sequenceA no) mn

> crossF ::  (Functor m, Functor o) =>
>            (a -> b -> c) -> o a -> m b -> Mat o m c
> crossF f as bs = (\ a -> f a <$> bs) <$> as

> dot ::  (Foldable n, Applicative n, Ord a, Num a) => 
>         n a -> n a -> a
> u `dot` v = sum (liftA2 (*) u v)

}
\frame{\frametitle{Represent via type family (old)}

> class  VectorSpace v => HasBasis v where
>   type Basis v :: *
>   coord :: v -> (Basis v -> Scalar v)

Linear map as memoized function from basis:

> newtype a :-* b = L (Basis a :->: b)

See
\href{http://conal.net/papers/beautiful-differentiation/}{\emph{Beautiful
differentiation}} (ICFP 2009).

}
\frame{\frametitle{Represent as GADT}

> data a :-* b where
>   Dot    ::  InnerSpace b =>
>              b -> (b :-* Scalar b)
>   (:&&)  ::  VS3 a c d =>  -- vector spaces with same scalar field
>              (a :-* c) -> (a :-* d) -> (a :-* c :* d)

}

\ssection{Semantics and implementation}

\frame{\frametitle{Semantics}

> apply :: (a :-* b) -> (a -> b)
> apply (Dot b)    = dot b
> apply (f :&& g)  = apply f &&& apply g

Recall:

> data a :-* b where
>   Dot    ::  InnerSpace b  => b -> (b :-* Scalar b)
>   (:&&)  ::  VS3 a c d     => (a :-* c) -> (a :-* d) -> (a :-* c :* d)

}
\frame{\frametitle{Semantic type class morphisms}

\fbox{\begin{minipage}[t]{0.45\textwidth}

|Category| instance specification:

> apply id       == id
> apply (g . f)  == apply g . apply f

\end{minipage}}
\fbox{\begin{minipage}[t]{0.4\textwidth}

|Arrow| instance specification:

> apply (f &&& g)  == apply f &&& apply g
> apply (f *** g)  == apply f *** apply g

\end{minipage}}

where

> (&&&)  :: Arrow (~>) => (a ~> c) -> (a ~> d) -> (a       ~> c :* d)
> (***)  :: Arrow (~>) => (a ~> c) -> (b ~> d) -> (a :* b  ~> c :* d)

The |Category| and |Arrow| laws then follow.

}
\frame{\frametitle{Deriving a |Category| instance}

One case:
\begin{center}
\fbox{\begin{minipage}[t]{0.45\textwidth}

>     apply ((f :&& g) . h)
> ==  (apply f &&& apply g) . apply h
> ==  apply f . apply h &&& apply g . apply h
> ==  apply (f . h &&& g . h)

\end{minipage}}
\end{center}

Uses:

> (f &&& g) . h == f . h &&& g . h

Implementation:

>   (f :&& g) . h = f . h :&& g . h

}
\frame{\frametitle{Deriving a |Category| instance}

\begin{center}
\fbox{\begin{minipage}[t]{0.35\textwidth}

>     apply (Dot s . Dot b)
> ==  dot s . dot b
> ==  dot (s *^ b)
> ==  apply (Dot (s *^ b))
> SPACE

\end{minipage}}
\fbox{\begin{minipage}[t]{0.55\textwidth}

>     apply (Dot (a,b) . (f :&& g))
> ==  dot (a,b) . (apply f &&& apply g)
> ==  add . (dot a . apply f &&& dot b . apply g)
> ==  dot a . apply f ^+^ dot b . apply g
> ==  apply (Dot a . f ^+^ Dot b . g)

\end{minipage}}
\end{center}

\vspace{-1ex}
Uses:

> dot (a,b)              == add . (dot a *** dot b)
>
> (k *** h) . (f &&& g)  == k . f &&& h . g

Implementation:

>  Dot s      . Dot b      = Dot (s *^ b)
>  Dot (a,b)  . (f :&& g)  = Dot a . f ^+^ Dot b . g

}
\frame{\frametitle{Deriving an |Arrow| instance}

\begin{center}
\fbox{\begin{minipage}[t]{0.35\textwidth}

>     SPACE
>     apply (f &&& g)
> ==  apply f &&& apply g
> ==  apply (f :&& g)
>     SPACE

\end{minipage}}
\fbox{\begin{minipage}[t]{0.5\textwidth}

>     apply (f *** g)
> ==  apply f *** apply g
> ==  apply f . fst &&& apply g . snd
> ==  apply (compFst f) &&& apply (compSnd g)
> ==  apply (compFst f :&& compSnd g)

\end{minipage}}
\end{center}

assuming

> apply (compFst  f)  == apply f  . fst
> apply (compSnd  g)  == apply g  . snd

\out{
Uses:

> f *** g == f . fst &&& g . snd

}

}
\frame{\frametitle{Composing with |fst| and |snd|}

> compFst  :: VS3 a b c => a :-* c -> a :* b :-* c
> compSnd  :: VS3 a b c => b :-* c -> a :* b :-* c

Derivation:

\begin{center}
\fbox{\begin{minipage}[t]{0.5\textwidth}

> dot a      . fst  == dot (a,0)
>
> (f &&& g)  . fst  == f . fst &&& g . fst
\end{minipage}}
\end{center}

Implementation:

> compFst  (Dot a)    = Dot (a,zeroV)
> compFst  (f :&& g)  = compFst f &&& compFst g

> compSnd  (Dot b)    = Dot (zeroV,b)
> compSnd  (f :&& g)  = compSnd f &&& compSnd g

}

\end{document}


%% ------------------ Junk

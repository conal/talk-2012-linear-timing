% -*- latex -*-
\documentclass{beamer}

% \usetheme{Warsaw} 

\usepackage{beamerthemesplit}

\useoutertheme{infolines}

\input{macros}

%include polycode.fmt
%include forall.fmt
%include greek.fmt
%include mine.fmt

\title{Some fun with linear transformations}
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

\ssection{Motivation}

\frame{\frametitle{Motivation}
\begin{itemize}

\item Circuit timing analysis
\item Package linear transformations as a category/arrow
\item Derive type class instances from simple semantics

\end{itemize}
}

\ssection{Representation}

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
\begin{pmatrix} a_{\one \one} & \cdots & a_{\one m} \\ \vdots & \ddots & \vdots \\ a_{n \one} & \cdots & a_{n m} \end{pmatrix}
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

|Category| instance specification:

> apply id       == id
> apply (g . f)  == apply g . apply f

|Arrow| instance specification:

> apply (f &&& g)  == apply f &&& apply g
> apply (f *** g)  == apply f *** apply g

|Category| and |Arrow| laws then follow.

}
\frame{\frametitle{Deriving a |Category| instance}

>     apply ((f :&& g) . h)
> ==  (apply f &&& apply g) . apply h
> ==  apply f . apply h &&& apply g . apply h
> ==  apply (f . h &&& g . h)

Uses:

> (f &&& g) . h == f . h &&& g . h

Implementation:

>   (f :&& g) . h = f . h :&& g . h

}
\frame{\frametitle{Deriving a |Category| instance}

>     apply (Dot s . Dot b)
> ==  dot s . dot b
> ==  dot (s *^ b)
> ==  apply (Dot (s *^ b))

>     apply (Dot (a,b) . (f :&& g))
> ==  dot (a,b) . (apply f &&& apply g)
> ==  add . (dot a . apply f &&& dot b . apply g)
> ==  dot a . apply f ^+^ dot b . apply g
> ==  apply (Dot a . f ^+^ Dot b . g)

\out{
Uses:

> dot s . dot b          == dot (s *^ b)  -- s must be scalar
>
> dot (a,b)              == add . (dot a *** dot b)
>
> (k *** h) . (f &&& g)  == k . f &&& h . g
}

Implementation:

>  Dot s      . Dot b      = Dot (s *^ b)
>  Dot (a,b)  . (f :&& g)  = Dot a . f ^+^ Dot b . g

}
\frame{\frametitle{Deriving an |Arrow| instance}

>     apply (f &&& g)
> ==  apply f &&& apply g
> ==  apply (f :&& g)

>     apply (f *** g)
> ==  apply f *** apply g
> ==  apply f . fst &&& apply g . snd
> ==  apply (compFst f) &&& apply (compSnd g)
> ==  apply (compFst f :&& compSnd g)

assuming

> apply (compFst f)  == apply f  . fst
> apply (compSnd g)  == apply g  . snd

\out{
Uses:

> f *** g == f . fst &&& g . snd

}

}
\frame{\frametitle{Composing with |fst| and |snd|}

> compFst  :: VS3 a b c => a :-* c -> a :* b :-* c
> compSnd  :: VS3 a b c => b :-* c -> a :* b :-* c

Derivation:

> dot a      . fst  == dot (a,0)
>
> (f &&& g)  . fst  == f . fst &&& g . fst

Implementation:

> compFst  (Dot a)    = Dot (a,zeroV)
> compFst  (f :&& g)  = compFst f &&& compFst g

> compSnd  (Dot b)    = Dot (zeroV,b)
> compSnd  (f :&& g)  = compSnd f &&& compSnd g

}
\ssection{Application to timing analysis}

\frame{\frametitle{Composing with |fst| and |snd|}

}

\end{document}


%% ------------------ Junk

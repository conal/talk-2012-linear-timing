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
% full date/venue is too long for infolines space
% \date{3 September, 2009 \hspace{1.5ex} Haskell Symposium}
\date{IFIP WG 2.8, November 2012}

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
\item Only handles |Rm :-* Rn|.
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

> data a :-* b where
>   Dot    ::  InnerSpace b =>
>              b -> (b :-* Scalar b)
>   (:&&)  ::  VS3 a c d =>  -- vector spaces with same scalar field
>              (a :-* c) -> (a :-* d) -> (a :-* c :* d)



}

\frame{\frametitle{Derive class instances via semantic morphisms}

}

\ssection{Application to timing analysis}

\end{document}


%% ------------------ Junk

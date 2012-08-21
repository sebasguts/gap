#############################################################################
##
#W  matrix.gd                   GAP library                     Thomas Breuer
#W                                                             & Frank Celler
#W                                                         & Alexander Hulpke
#W                                                           & Heiko Theissen
#W                                                         & Martin Schoenert
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
#Y  Copyright (C) 2002 The GAP Group
##
##  This file contains those functions that mainly deal with matrices.
##
Revision.matrix_gd :=
    "@(#)$Id$";


#############################################################################
##
#V  InfoMatrix
##
##  The info class for matrix operations is `InfoMatrix'.
##
DeclareInfoClass( "InfoMatrix" );

#############################################################################
##
#F  PrintArray( <array> )
##
##  pretty-prints the array <array>.
##
DeclareGlobalFunction("PrintArray");

#############################################################################
##
#P  IsGeneralizedCartanMatrix( <A> )
##
##  The square matrix <A> is a generalized Cartan Matrix if and only if
##  1. `A[i][i] = 2' for all $i$,
##  2. `A[i][j]' are nonpositive integers for $i \not= j$,
##  3. `A[i][j] = 0' implies `A[j][i] = 0'.
##
DeclareProperty( "IsGeneralizedCartanMatrix", IsMatrix );


#############################################################################
##
#O  IsDiagonalMat( <mat> )
##
##  returns true if mat has only zero entries off the main diagonal, false
##  otherwise.
##
DeclareOperation("IsDiagonalMat",[IsMatrix]);

#############################################################################
##
#O  IsUpperTriangularMat( <mat> )
##
##  returns true if mat has only zero entries below the main diagonal, false
##  otherwise.
##
DeclareOperation("IsUpperTriangularMat",[IsMatrix]);

#############################################################################
##
#O  IsLowerTriangularMat( <mat> )
##
##  returns true if mat has only zero entries below the main diagonal, false
##  otherwise.
##
DeclareOperation("IsLowerTriangularMat",[IsMatrix]);

#############################################################################
##
#O  DiagonalOfMat( <mat> )
##
##  returns the diagonal of <mat> as a list.
##
DeclareGlobalFunction( "DiagonalOfMat" );


#############################################################################
##
#A  AbelianInvariantsOfList( <list> ) . . . . .  abelian invariants of a list
##
DeclareAttribute( "AbelianInvariantsOfList", IsCyclotomicCollection );

#############################################################################
##
#A  BaseMat( <mat> )  . . . . . . . . . .  base for the row space of a matrix
##
##  returns a basis for the row space generated by the rows of <mat> in the
##  form of an immutable matrix.
##
DeclareAttribute( "BaseMat", IsMatrix );

#############################################################################
##
#O  BaseMatDestructive( <mat> )
##
##  Does the same as `BaseMat', with the difference that it may destroy
##  the matrix <mat>. The matrix <mat> must be mutable.
##
DeclareOperation( "BaseMatDestructive", [ IsMatrix ] );

#############################################################################
##
#A  BaseOrthogonalSpaceMat( <mat> )
##
##  Let $V$ be the row space generated  by the rows of  <mat> (over any field
##  that contains all  entries of <mat>).  `BaseOrthogonalSpaceMat( <mat>  )'
##  computes a base of the orthogonal space of $V$.
##
##  The rows of <mat> need not be linearly independent.
##
#T Note that this means to transpose twice ...
##
DeclareAttribute( "BaseOrthogonalSpaceMat", IsMatrix );


#############################################################################
##
#A  DefaultFieldOfMatrix( <mat> )
##
##  For a matrix <mat>, `DefaultFieldOfMatrix' returns either a field
##  (not necessarily the smallest one) containing all entries of <mat>,
##  or `fail'.
##
##  If <mat> is a matrix of finite field elements or a matrix of cyclotomics,
##  `DefaultFieldOfMatrix' returns the default field generated by the matrix
##  entries (see~"Creating Finite Fields" and "Operations for Cyclotomics").
##
DeclareAttribute( "DefaultFieldOfMatrix", IsMatrix );


#############################################################################
##
#A  DepthOfUpperTriangularMatrix( <mat> )
##
##  If <mat> is an upper triangular matrix this attribute returns the
##  index of the first nonzero diagonal.
##
DeclareAttribute( "DepthOfUpperTriangularMatrix", IsMatrix );


#############################################################################
##
#A  DeterminantMat( <mat> ) . . . . . . . . . . . . . determinant of a matrix
#F  Determinant( <mat> )
##
##  returns the determinant of the square matrix <mat>.
##
##  These methods assume implicitly that <mat> is defined over an
##  integral domain whose quotient field is implemented in {\GAP}. For
##  matrices defined over an arbitrary commutative ring with one 
##  see~"DeterminantMatDivFree".
##
DeclareAttribute( "DeterminantMat", IsMatrix );

#############################################################################
##
#O  DeterminantMatDestructive( <mat> )
##
##  Does the same as `DeterminantMat', with the difference that it may
##  destroy its argument. The matrix <mat> must be mutable.
##
DeclareOperation( "DeterminantMatDestructive", [ IsMatrix and IsMutable] );

#############################################################################
##
#O  DeterminantMatDivFree( <mat> )
##
##  returns the determinant of a square matrix <mat> over an arbitrary 
##  commutative ring with one using the division free method of 
##  Mahajan and Vinay \cite{MV97}.
##  
DeclareOperation("DeterminantMatDivFree",[IsMatrix]);

#############################################################################
##
#A  DimensionsMat( <mat> )  . . . . . . . . . . . . .  dimensions of a matrix
##
##  is a list of length 2, the first being the number of rows, the second
##  being the number of columns of the matrix <mat>.
##
DeclareAttribute( "DimensionsMat", IsMatrix );


#############################################################################
##
#O  ElementaryDivisorsMat([<ring>,] <mat>)
##
##  `ElementaryDivisors' returns a list of the elementary divisors, i.e., the
##  unique <d> with `<d>[<i>]' divides  `<d>[<i>+1]' and <mat> is  equivalent
##  to a diagonal matrix with the elements `<d>[<i>]' on the diagonal.
##  The operations are performed over the ring <ring>, which must contain
##  all matrix entries. For compatibility reasons it can be omitted and
##  defaults to `Integers'.
##
DeclareOperation( "ElementaryDivisorsMat", [IsRing,IsMatrix] );

#############################################################################
##
#O  TriangulizedNullspaceMatNT(<mat>)
##
##  This returns the triangulized nullspace of the matrix <mat>, without
##  transposing it. This is used in `TriangulizedNullspaceMat', and
##  `TriangulizedNullspaceMatDestructive'.
##
DeclareOperation( "TriangulizedNullspaceMatNT", [ IsMatrix ] );


#############################################################################
##
#A  NullspaceMat( <mat> ) . . . . . . basis of solutions of <vec> * <mat> = 0
#A  TriangulizedNullspaceMat(<mat>)
##
##  returns a list of row vectors that form a basis of the vector space of
##  solutions to the equation `<vec>*<mat>=0'. The result is an immutable
##  matrix. This basis is not guaranteed to be in any specific form.
##
##  The variant `TriangulizedNullspaceMat' returns a basis of the nullspace
##  in triangulized form as is often needed for algorithms.
##
DeclareAttribute( "NullspaceMat", IsMatrix );
DeclareAttribute( "TriangulizedNullspaceMat", IsMatrix );

#############################################################################
##
#O  NullspaceMatDestructive( <mat> )
#O  TriangulizedNullspaceMatDestructive(<mat>)
##
##  This function does the same as `NullspaceMat'. However, the latter function
##  makes a copy of <mat> to avoid having to change it. This function
##  does not do that; it returns the null space and may destroy <mat>;
##  this saves a lot of memory in case <mat> is big. The matrix <mat>
##  must be mutable.
##
##  The variant `TriangulizedNullspaceMatDestructive' returns a basis of the
##  nullspace in triangulized form. It may destroy the matrix <mat>.
##
DeclareOperation( "NullspaceMatDestructive", [ IsMatrix and IsMutable] );
DeclareOperation( "TriangulizedNullspaceMatDestructive", [ IsMatrix and IsMutable] );


#############################################################################
##
#O  GeneralisedEigenvalues( <F>, <A> )
#O  GeneralizedEigenvalues( <F>, <A> )
##
##  The generalised eigenvalues of the matrix <A> over the field <F>.
##
DeclareOperation( "GeneralisedEigenvalues", [ IsRing, IsMatrix ] );
DeclareSynonym( "GeneralizedEigenvalues", GeneralisedEigenvalues );

#############################################################################
##
#O  GeneralisedEigenspaces( <F>, <A> )
#O  GeneralizedEigenspaces( <F>, <A> )
##
##  The generalised eigenspaces of the matrix <A> over the field <F>.
##
DeclareOperation( "GeneralisedEigenspaces", [ IsRing, IsMatrix ] );
DeclareSynonym( "GeneralizedEigenspaces", GeneralisedEigenspaces );


#############################################################################
##
#O  Eigenvalues( <F>, <A> )
##
##  The eigenvalues of the matrix <A> over the field <F>.
##
DeclareOperation( "Eigenvalues", [ IsRing, IsMatrix ] );

#############################################################################
##
#O  Eigenspaces( <F>, <A> )
##
##  The eigenspaces of the matrix <A> over the field <F>.
##
DeclareOperation( "Eigenspaces", [ IsRing, IsMatrix ] );

#############################################################################
##
#O  Eigenvectors( <F>, <A> )
##
##  The eigenspaces of the matrix <A> over the field <F>.
##
DeclareOperation( "Eigenvectors", [ IsRing, IsMatrix ] );


#############################################################################
##
#A  ProjectiveOrder( <mat> )
##
##  Returns an integer n and a finite field element e such that <A>^n = eI.
##  <mat> must be a matrix defined over a finite field.
##
DeclareAttribute( "ProjectiveOrder", IsMatrix );

#############################################################################
##
#F  OrderMatTrial( <mat>,<lim> )
##
##  tries to compute the order of <mat> (of small order) by mapping the
##  basis vectors under <mat>. This is done at most <lim> times, if the
##  matrix order has not been determined at this point (or if the matrix is
##  not invertible) `fail' is returned.
##
DeclareGlobalFunction( "OrderMatTrial" );


#############################################################################
##
#A  RankMat( <mat> )  . . . . . . . . . . . . . . . . . . .  rank of a matrix
##
##  If <mat> is a matrix whose rows span a free module over the ring
##  generated by the matrix entries and their inverses
##  then `RankMat' returns the dimension of this free module.
##  Otherwise `fail' is returned.
##
##  Note that `RankMat' may perform a Gaussian elimination.
##  For large rational matrices this may take very long,
##  because the entries may become very large.
##
DeclareAttribute( "RankMat", IsMatrix );

#############################################################################
##
#O  RankMatDestructive( <mat> )  . . . . . . . . . . . . .  rank of a matrix
##
##  `RankMatDestructive' returns the same result as "RankMat" but may
##  modify its argument in the process, if this saves time or memory
##
DeclareOperation( "RankMatDestructive", [IsMatrix and IsMutable]);


#############################################################################
##
#A  SemiEchelonMat( <mat> )
##
##  A matrix over a field $F$ is in semi-echelon form if the first nonzero
##  element in each row is the identity of $F$,
##  and all values exactly below these pivots are the zero of $F$.
##
##  `SemiEchelonMat' returns a record that contains information about
##  a semi-echelonized form of the matrix <mat>.
##
##  The components of this record are
##
##  \beginitems
##  `vectors'&
##        list of row vectors, each with pivot element the identity of $F$,
##
##  `heads'&
##        list that contains at position <i>, if nonzero, the number of the
##        row for that the pivot element is in column <i>.
##  \enditems
##
DeclareAttribute( "SemiEchelonMat", IsMatrix );

#############################################################################
##
#O  SemiEchelonMatDestructive( <mat> )
##
##  This does the same as `SemiEchelonMat( <mat> )', except that it may
##  (and probably will) destroy the matrix <mat>.
##
DeclareOperation( "SemiEchelonMatDestructive", [ IsMatrix and IsMutable] );


#############################################################################
##
#A  SemiEchelonMatTransformation( <mat> )
##
##  does the same as `SemiEchelonMat' but additionally stores the linear
##  transformation $T$ performed on the matrix.
##  The additional components of the result are
##
##  \beginitems
##  `coeffs'&
##        a list of coefficients vectors of the `vectors' component,
##        with respect to the rows of <mat>, that is, `coeffs * mat'
##        is the `vectors' component.
##
##  `relations'&
##        a list of basis vectors for the (left) null space of <mat>.
##  \enditems
##
DeclareAttribute( "SemiEchelonMatTransformation", IsMatrix );

#############################################################################
##
#O  SemiEchelonMatTransformationDestructive( <mat> )
##
##  This does the same as `SemiEchelonMatTransformation( <mat> )', except that it may
##  (and probably will) destroy the matrix <mat>.
##
DeclareOperation( "SemiEchelonMatTransformationDestructive", [
        IsMatrix and IsMutable ] );


#############################################################################
##
#F  SemiEchelonMatsNoCo( <mats> )
##
##  The function that does the work for `SemiEchelonMats' and
##  `SemiEchelonMatsDestructive'.
##
DeclareGlobalFunction( "SemiEchelonMatsNoCo" );

#############################################################################
##
#O  SemiEchelonMats( <mats> )
##
##  A list of matrices over a field $F$ is in semi-echelon form if the
##  list of row vectors obtained on concatenating the rows of each matrix
##  is a semi-echelonized matrix (see "SemiEchelonMat").
##
##  `SemiEchelonMats' returns a record that contains information about
##  a semi-echelonized form of the list <mats> of matrices.
##
##  The components of this record are
##
##  \beginitems
##  `vectors'&
##        list of matrices, each with pivot element the identity of $F$,
##
##  `heads'&
##        matrix that contains at position [<i>,<j>], if nonzero,
##        the number of the matrix that has the pivot element in
##        this position
##  \enditems
##
DeclareOperation( "SemiEchelonMats", [ IsList ] );

#############################################################################
##
#O  SemiEchelonMatsDestructive( <mats> )
##
##  Does the same as `SemiEchelonmats', except that it may destroy
##  its argument. Therefore the argument must be a list of matrices
##  that re mutable.
##
DeclareOperation( "SemiEchelonMatsDestructive", [ IsList ] );


#############################################################################
##
#A  TransposedMatImmutable( <mat> ) . . . . . . . . .  transposed of a matrix
#A  TransposedMatAttr( <mat> )  . . . . . . . . . . .  transposed of a matrix
#A  TransposedMat( <mat> )  . . . . . . . . . . . . .  transposed of a matrix
#O  TransposedMatMutable( <mat> ) . . . . . . . . . .  transposed of a matrix
#O  TransposedMatOp( <mat> )  . . . . . . . . . . . .  transposed of a matrix
##
##  These functions all return the transposed of the matrix <mat>, i.e.,
##  a matrix <trans> such that `<trans>[<i>][<k>] = <mat>[<k>][<i>]' holds.
##
##  They differ only w.r.t. the mutability of the result.
##
##  `TransposedMat' is an attribute and hence returns an immutable result.
##  `TransposedMatMutable' is guaranteed to return a new *mutable* matrix.
##
##  `TransposedMatImmutable' and `TransposedMatAttr' are synonyms of
##  `TransposedMat',
##  and `TransposedMatOp' is a synonym of `TransposedMatMutable',
##  in analogy to operations such as `Zero' (see~"Zero").
##
DeclareAttribute( "TransposedMatImmutable", IsMatrix );

DeclareSynonymAttr( "TransposedMatAttr", TransposedMatImmutable );
DeclareSynonymAttr( "TransposedMat", TransposedMatImmutable );

DeclareOperation( "TransposedMatMutable", [ IsMatrix ] );
DeclareSynonym( "TransposedMatOp", TransposedMatMutable );
DeclareSynonym( "MutableTransposedMat", TransposedMatMutable ); # needed?


#############################################################################
##
#O  MutableTransposedMatDestructive( <mat> )
##
##  `MutableTransposedMatDestructive' returns the transpose of the mutable
##  matrix <mat>. It may, but does not have to, destroy the contents
##  of <mat> in the process. In particular, the returned matrix may be 
##  identical to <mat>, having been transposed in place.
##
DeclareOperation( "MutableTransposedMatDestructive", [IsMatrix and IsMutable] );


#############################################################################
##
#O  TransposedMatDestructive( <mat> )
##
##  If <mat> is a mutable matrix, then the transposed
##  is computed by swapping the entries in <mat>. In this way <mat> gets
##  changed. In all other cases the transposed is computed by `TransposedMat'.
##
DeclareOperation( "TransposedMatDestructive", [ IsMatrix ] );



############################################################################
##
#P  IsMonomialMatrix( <mat> )
##
##  A matrix is monomial if  and only if it  has exactly one nonzero entry in
##  every row and every column.
##
DeclareProperty( "IsMonomialMatrix", IsMatrix );


#############################################################################
##
#O  InverseMatMod( <mat>, <obj> )
##
##  For a square matrix <mat>, `InverseMatMod' returns a matrix <inv>
##  such that `<inv> * <mat>' is congruent to the identity matrix modulo
##  <obj>, if such a matrix exists, and `fail' otherwise.
##
DeclareOperation( "InverseMatMod", [ IsMatrix, IsObject ] );


#############################################################################
##
#O  KroneckerProduct( <mat1>, <mat2> )
##
##  The Kronecker product of two matrices is the matrix obtained when
##  replacing each entry <a> of <mat1> by the product `<a>*<mat2>' in one
##  matrix.
##
DeclareOperation( "KroneckerProduct", [ IsMatrix, IsMatrix ] );

#############################################################################
##
#O  SolutionMatNoCo( <mat>, <vec> )
##
##  Does thework for `SolutionMat' and `SolutionMatDestructive'.
##
DeclareOperation( "SolutionMatNoCo", [ IsMatrix, IsRowVector ] );


#############################################################################
##
#O  SolutionMat( <mat>, <vec> ) . . . . . . . . . .  one solution of equation
##
##  returns a row vector <x> that is a solution of the equation `<x> * <mat>
##  = <vec>'. It returns `fail' if no such vector exists.
##
DeclareOperation( "SolutionMat", [ IsMatrix, IsRowVector ] );

#############################################################################
##
#O  SolutionMatDestructive( <mat>, <vec> )
##
##  Does the same as `SolutionMat( <mat>, <vec> )' except that it may
##  destroy the matrix <mat>. The matrix <mat> must be mutable.
##
DeclareOperation( "SolutionMatDestructive", [ IsMatrix and IsMutable, IsRowVector ] );



############################################################################
##
#O  SumIntersectionMat( <M1>, <M2> )  . .  sum and intersection of two spaces
##
##  performs  Zassenhaus'  algorithm to compute  bases  for  the sum  and the
##  intersection of spaces generated by the rows of the matrices <M1>, <M2>.
##
##  returns a list  of length 2,   at first position   a base of the sum,  at
##  second  position a  base   of the   intersection.   Both  bases  are   in
##  semi-echelon form (see~"Echelonized matrices").
##
DeclareOperation( "SumIntersectionMat", [ IsMatrix, IsMatrix ] );


#############################################################################
##
#O  TriangulizeMat( <mat> ) . . . . . bring a matrix in upper triangular form
##
##  applies the Gaussian Algorithm to the mutable matrix <mat> and changes
##  <mat> such that it is in upper triangular
##  normal form (sometimes called ``Hermite normal form'').
##
DeclareOperation( "TriangulizeMat", [ IsMatrix and IsMutable ] );

#############################################################################
##
#F  TriangulizeMatGF2( <mat> ). . . . bring a matrix in upper triangular form
##
##  special function for the GF2 case
##
DeclareGlobalFunction("TriangulizeMatGF2");


#############################################################################
##
#O  UpperSubdiagonal( <mat>, <pos> )
##
##  returns a mutable list containing the entries of the <pos>th upper
##  subdiagonal of <mat>.
##
DeclareOperation( "UpperSubdiagonal", [ IsMatrix, IsPosInt ] );


#############################################################################
##
#F  BaseFixedSpace( <mats> )  . . . . . . . . . . . .  calculate fixed points
##
##  `BaseFixedSpace' returns a list of row vectors that form a base of the
##  vector space $V$ such that $v M = v$ for all $v$ in $V$ and all matrices
##  $M$ in the list <mats>.  (This is the common eigenspace of all matrices
##  in <mats> for the eigenvalue 1.)
##
DeclareGlobalFunction( "BaseFixedSpace" );


#############################################################################
##
#F  BaseSteinitzVectors( <bas>, <mat> )
##
##  find vectors extending mat to a basis spanning the span of <bas>.
##  Both <bas> and <mat> must be matrices of full (row) rank. It returns a
##  record with the following components:
##  \beginitems
##  `subspace'&is a basis of the space spanned by <mat> in upper triangular
##  form with leading ones at all echelon steps and zeroes above these ones.
##
##  `factorspace'& is a list of extending vectors in upper triangular form.
##
##  `factorzero'& is a zero vector.
##
##  `heads'& is a list of integers which can be used to decompose vectors in
##  the basis vectors. The <i>th entry indicating the vector
##  that gives an echelon step at position <i>.
##  A negative number indicates an echelon step in the subspace, a positive
##  number an echelon step in the complement, the absolute value gives the
##  position of the vector in the lists `subspace' and `factorspace'.
##  \enditems
##
DeclareGlobalFunction( "BaseSteinitzVectors" );


#############################################################################
##
#F  BlownUpMat( <B>, <mat> )
##
##  Let <B> be a basis of a field extension $F / K$,
##  and <mat> a matrix whose entries are all in $F$.
##  (This is not checked.)
##  `BlownUpMat' returns a matrix over $K$ that is obtained by replacing each
##  entry of <mat> by its regular representation w.r.t.~<B>.
##
##  More precisely,
##  regard <mat> as the matrix of a linear transformation on the row space
##  $F^n$ w.r.t.~the $F$-basis with vectors $(v_1, ldots, v_n)$, say,
##  and suppose that the basis <B> consists of the vectors
##  $(b_1,  \ldots, b_m)$;
##  then the returned matrix is the matrix of the linear transformation
##  on the row space $K^{mn}$ w.r.t.~the $K$-basis whose vectors are
##  $(b_1 v_1, \ldots b_m v_1, \ldots, b_m v_n)$.
##
##  Note that the linear transformations act on *row* vectors, i.e.,
##  each row of the matrix is a concatenation of vectors of <B>-coefficients.
##
DeclareGlobalFunction( "BlownUpMat" );


#############################################################################
##
#F  BlownUpVector( <B>, <vector> )
##
##  Let <B> be a basis of a field extension $F / K$,
##  and <vector> a row vector whose entries are all in $F$.
##  `BlownUpVector' returns a row vector over $K$ that is obtained by
##  replacing each entry of <vector> by its coefficients w.r.t.~<B>.
##
##  So `BlownUpVector' and `BlownUpMat' (see~"BlownUpMat") are compatible
##  in the sense that for a matrix <mat> over $F$,
##  `BlownUpVector( <B>, <mat> \* <vector> )'
##  is equal to
##  `BlownUpMat( <B>, <mat> ) \* BlownUpVector( <B>, <vector> )'.
##
DeclareGlobalFunction( "BlownUpVector" );


#############################################################################
##
#F  DiagonalizeIntMatNormDriven(<mat>)  . . . . diagonalize an integer matrix
##
##  `DiagonalizeIntMatNormDriven'  diagonalizes  the  integer  matrix  <mat>.
##
##  It tries to keep the entries small  through careful  selection of pivots.
##
##  First it selects a nonzero entry for which the  product of row and column
##  norm is minimal (this need not be the entry with minimal absolute value).
##  Then it brings this pivot to the upper left corner and makes it positive.
##
##  Next it subtracts multiples of the first row from the other rows, so that
##  the new entries in the first column have absolute value at most  pivot/2.
##  Likewise it subtracts multiples of the 1st column from the other columns.
##
##  If afterwards not  all new entries in the  first column and row are zero,
##  then it selects a  new pivot from those  entries (again driven by product
##  of norms) and reduces the first column and row again.
##
##  If finally all offdiagonal entries in the first column  and row are zero,
##  then it  starts all over again with the submatrix  `<mat>{[2..]}{[2..]}'.
##
##  The original idea is explained in ~\cite{HM97}.
##
##  \beginexample
##  gap> m:=[[14,20],[6,9]];;
##  gap> DiagonalizeIntMatNormDriven(m);
##  gap> m;
##  [ [ 2, 0 ], [ 0, 3 ] ]
##  \endexample
DeclareGlobalFunction( "DiagonalizeIntMatNormDriven" );

DeclareSynonym( "DiagonalizeIntMat", DiagonalizeIntMatNormDriven );


#############################################################################
##
#O  DiagonalizeMat(<ring>,<mat>)
##
##  brings the mutable matrix <mat>, considered as a matrix over <ring>,
##  into diagonal form by elementary row and column operations.
##
DeclareOperation( "DiagonalizeMat", [IsRing,IsMatrix and IsMutable] );


#############################################################################
##
#F  IdentityMat( <m> [, <F>] )  . . . . . . . identity matrix of a given size
##
##  returns a (mutable) <m>$\times$<m> identity matrix over the field given
##  by <F> (i.e. the smallest field containing the element <F> or <F> itself
##  if it is a field).
##
DeclareGlobalFunction( "IdentityMat" );


#############################################################################
##
#F  MutableCopyMat( <mat> ) . . . . . . . . . .  Copies  a matrix
##
##  `MutableCopyMat'  returns a fully mutable copy  of  the  matrix <mat>.
##
DeclareGlobalFunction( "MutableCopyMat" );


#############################################################################
##
#F  MutableIdentityMat( <m> [, <F>] ) mutable identity matrix of a given size
##
##  returns a (mutable) <m>$\times$<m> identity matrix over the field given
##  by <F>.
##  This is identical to `IdentityMat' and is present in {\GAP}~4.1
##  only for the sake of compatibility with beta-releases.
##  It should *not* be used in new code.
##
DeclareSynonym( "MutableIdentityMat", IdentityMat );


#############################################################################
##
#F  NullMat( <m>, <n> [, <F>] ) . . . . . . . . . null matrix of a given size
##
##  returns a (mutable) <m>$\times$<n> null matrix over the field given by
##  <F>.
##
DeclareGlobalFunction( "NullMat" );


#############################################################################
##
#F  MutableNullMat( <m>, <n>  [, <F>] ) mutable null matrix of a given size
##
##  returns a (mutable) <m>$\times$<n> null matrix over the field given
##  by <F>.
##  This is identical to `NullMat' and is present in {\GAP}~4.1
##  only for the sake of compatibility with beta-releases.
##  It should *not* be used in new code.
##
DeclareSynonym( "MutableNullMat", NullMat );


#############################################################################
##
#F  NullspaceModQ( <E>, <q> ) . . . . . . . . . . . .nullspace of <E> mod <q>
##
##  <E> must be a matrix of integers and <q> a prime power.
##  Then `NullspaceModQ' returns the set of all vectors of integers modulo
##  <q>, which solve the homogeneous equation system given by <E> modulo <q>.
##
DeclareGlobalFunction( "NullspaceModQ" );


#############################################################################
##
#F  BasisNullspaceModN( <M>, <n> ) . . . . . . .  .  nullspace of <E> mod <n>
##
##  <M> must be a matrix of integers modulo <n> and <n> a positive integer.  
##  Then 'NullspaceModQ' returns a set <B> of vectors such that every <v> 
##  such that <v> <M> = 0 modulo <n> can be expressed by a Z-linear combination
##  of elements of <M>.
##
DeclareGlobalFunction ("BasisNullspaceModN");


#############################################################################
##
#F  PermutationMat( <perm>, <dim> [, <F> ] ) . . . . . .  permutation matrix
##
##  returns a matrix in dimension <dim> over the field given by <F> (i.e.
##  the smallest field containing the element <F> or <F> itself if it is a
##  field)  that
##  represents the permutation <perm> acting by permuting the basis vectors
##  as it permutes points.
##
DeclareGlobalFunction( "PermutationMat" );


#############################################################################
##
#F  DiagonalMat( <vector> ) . . . . . . . . . . . . . . . . . diagonal matrix
##
##  returns a diagonal matrix <mat> with the diagonal entries given by
##  <vector>.
##
DeclareGlobalFunction( "DiagonalMat" );


#############################################################################
##
#F  ReflectionMat( <coeffs> )
#F  ReflectionMat( <coeffs>, <root> )
#F  ReflectionMat( <coeffs>, <conj> )
#F  ReflectionMat( <coeffs>, <conj>, <root> )
##
##  Let <coeffs> be a row vector.
##  `ReflectionMat' returns the matrix of the reflection in this vector.
##
##  More precisely, if <coeffs> is the coefficients of a vector $v$ w.r.t. a
##  basis $B$ (see~"Basis"), say, then the returned matrix describes the
##  reflection in $v$ w.r.t. $B$ as a map on a row space, with action from
##  the right.
##
##  The optional argument <root> is a root of unity that determines the order
##  of the reflection.  The default is a reflection of order 2.
##  For triflections one should choose a third root of unity etc.
##  (see~"ref:E").
##
##  <conj> is a function of one argument that conjugates a ring element.
##  The default is `ComplexConjugate'.
##
##  The matrix of the reflection in $v$ is defined as
##  $$
##  M = I_n + \overline{v^{tr}} . \frac{w-1}{v \overline{v^{tr}}} . v
##  $$
##  where `$w$ = root',
##  $n$ is the length of the coefficient list,
##  and `$\overline{\vphantom{x}}$' denotes the conjugation.
##
DeclareGlobalFunction( "ReflectionMat" );


#############################################################################
##
#F  RandomInvertibleMat( <m> [, <R>] )  . . . make a random invertible matrix
##
##  `RandomInvertibleMat' returns a new mutable invertible random
##  matrix with <m> rows and columns with elements taken from the ring
##  <R>, which defaults to `Integers'.
##
DeclareGlobalFunction( "RandomInvertibleMat" );


#############################################################################
##
#F  RandomMat( <m>, <n> [, <R>] ) . . . . . . . . . . .  make a random matrix
##
##  `RandomMat' returns a new mutable random matrix with <m> rows and
##  <n> columns with elements taken from the ring <R>, which defaults
##  to `Integers'.
##
DeclareGlobalFunction( "RandomMat" );


#############################################################################
##
#F  RandomUnimodularMat( <m> )  . . . . . . . . . .  random unimodular matrix
##
##  returns a new random mutable <m>$\times$<m> matrix with integer
##  entries that is invertible over the integers.
##
DeclareGlobalFunction( "RandomUnimodularMat" );


#############################################################################
##
#F  SimultaneousEigenvalues( <matlist>, <expo> ) . . . . . . . . .eigenvalues
##
##  The matrices in  <matlist>  must  be matrices over GF(<q>) for some
##  prime <q>.  Together, they must  generate an  abelian p-group  of
##  exponent <expo>.
##  Then the eigenvalues of <mat>  in the splitting field `GF(<q>^<r>)' for
##  some <r> are powers of an element $\xi$ in the splitting field, which is
##  of order  <expo>.  `SimultaneousEigenvalues' returns a matrix of
##  integers  mod <expo>, say $(a_{i,j})$,  such that the power
##  $\xi^{a_{i,j}}$ is an eigenvalue of the <i>-th matrix in  <matlist> and
##  the eigenspaces of the different matrices to the eigenvalues
##  $\xi^{a_{i,j}}$ for fixed <j> are equal.
##
DeclareGlobalFunction( "SimultaneousEigenvalues" );


#############################################################################
##
#F  TraceMat( <mat> ) . . . . . . . . . . . . . . . . . . . trace of a matrix
#F  Trace( <mat> )
##
##  The trace of a square matrix is the sum of its diagonal entries.
##
DeclareGlobalFunction( "TraceMat" );


#############################################################################
##
#A  JordanDecomposition( <mat> )
##
##  `JordanDecomposition( <mat > )' returns a list `[S,N]' such that
##  `S' is a semisimple matrix and `N' is nilpotent. Furthermore, `S'
##  and `N' commute and `<mat>=S+N'.
##
DeclareAttribute( "JordanDecomposition", IsMatrix );


#############################################################################
##
#F  FlatBlockMat( <blockmat> ) . . . . . . . . convert block matrix to matrix
##
DeclareGlobalFunction( "FlatBlockMat" );

#############################################################################
##
#F  DirectSumMat( <matlist> ) . . . . . . . . . . . create block diagonal mat
##
DeclareGlobalFunction( "DirectSumMat" );

#############################################################################
##
#F  EmptyMatrix( <char> )
##
##  is an empty (ordinary) matrix in characteristic <char> that can be added
##  to or multiplied with empty lists (representing zero-dimensional row
##  vectors). It also acts (via `^') on empty lists.
##
#T store in the family as an attribute?
##
DeclareGlobalFunction( "EmptyMatrix" );


#############################################################################
##
#F  OnSubspacesByCanonicalBasis(<bas>,<mat>)
##
##  implements the operation of a matrix group on subspaces of a vector
##  space. <bas> must be a list of (linearly independent) vectors which
##  forms a basis of the subspace in Hermite normal form. <mat> is an
##  element of the acting matrix group. The function returns a mutable
##  matrix which gives the basis of the image of the subspace in Hermite
##  normal form. (In other words: it triangulizes the product of <bas> with
##  <mat>.)
##
DeclareGlobalFunction("OnSubspacesByCanonicalBasis");


#############################################################################
##
#F  OnSubspacesByCanonicalBasisGF2(<bas>,<mat>)
##
##  is a special version of `OnSubspacesByCanonicalBasis' for matrices over
##  GF2.
##
DeclareSynonym("OnSubspacesByCanonicalBasisGF2",OnSubspacesByCanonicalBasis);


#############################################################################
##
#A  CharacteristicPolynomial( <mat> )
#O  CharacteristicPolynomial( [<F>, ]<mat>[, <ind>] )
##
##  For a square matrix <mat>, `CharacteristicPolynomial' returns the
##  *characteristic polynomial* of <mat>, that is, the `StandardAssociate'
##  of the determinant of the
##  matrix $<mat> - X \cdot I$, where $X$ is an indeterminate and $I$ is the
##  appropriate identity matrix.
##
##  If a field <F> is given as first argument then the characteristic
##  polynomial of the <F>-linear mapping induced by <mat> is computed.
##  If <F> contains the entries of <mat> then this is of course the same
##  polynomial as the one computed by the one argument version;
##  if <F> is a proper subfield of the default field
##  (see~"DefaultFieldOfMatrix") of <mat> then the characteristic polynomial
##  is computed using `BlownUpMat' (see~"BlownUpMat").
##
##  The returned polynomials are expressed in the indeterminate number <ind>.
##  If <ind> is not given, it defaults to $1$.
##
##  The characteristic polynomial is a multiple of the minimal polynomial
##  (see~"MinimalPolynomial").
##
DeclareAttribute( "CharacteristicPolynomial", IsMatrix );
DeclareOperation( "CharacteristicPolynomial", [ IsRing, IsMatrix ] );
DeclareOperation( "CharacteristicPolynomial", [ IsMatrix, IsPosInt ] );
DeclareOperation( "CharacteristicPolynomial",
    [ IsRing, IsMatrix, IsPosInt ] );


#############################################################################
##
#O  CharacteristicPolynomialMatrixNC( <field>,<mat>,<indnum> )
##
##  returns the characteristic polynomial for matrix <mat> which *must* be
##  defined over <field>. No tests are performed.
DeclareOperation("CharacteristicPolynomialMatrixNC",
  #IsField is not yet known
  [IsRing,IsOrdinaryMatrix,IsPosInt]);


#############################################################################
##
#O  MinimalPolynomialMatrixNC( <field>,<mat>,<indnum> )
##
##  returns the minimal polynomial for matrix <mat> which *must* be
##  defined over field>. No tests are performed.
DeclareOperation("MinimalPolynomialMatrixNC",
  #IsField is not yet known
  [IsRing,IsOrdinaryMatrix,IsPosInt]);

#############################################################################
##
#O  FieldOfMatrixList( <matlist> )
##
##  The smallest  field containing all the entries of all matrices in
##  <matlist>. As the algorithm must run through all matrix entries, this
##  can be hard.
##
DeclareOperation("FieldOfMatrixList",[IsListOrCollection]);

#############################################################################
##
#E


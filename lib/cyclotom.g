#############################################################################
##
#W  cyclotom.g                   GAP library                    Thomas Breuer
#W                                                             & Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file deals with cyclotomics.
##
Revision.cyclotom_g :=
    "@(#)$Id$";


#############################################################################
##
#C  IsCyclotomic( <obj> ) . . . . . . . . . . . . category of all cyclotomics
#C  IsCyc( <obj> )
##
##  Every object in the family `CyclotomicsFamily' lies in the category
##  `IsCyclotomic'.
##  This covers integers, rationals, proper cyclotomics, and the object
##  `infinity' (see~"Infinity").
##  All these objects except `infinity' lie also in the category `IsCyc',
##  `infinity' lies in (and can be detected from) the category `IsInfinity'.
##
DeclareCategory( "IsCyclotomic",
    IsScalar and IsAssociativeElement and IsCommutativeElement );

DeclareCategoryKernel( "IsCyc", IsCyclotomic, IS_CYC );


#############################################################################
##
#C  IsCyclotomicCollection  . . . . . . category of collection of cyclotomics
#C  IsCyclotomicCollColl  . . . . . . .  category of collection of collection
#C  IsCyclotomicCollCollColl  . . . .  category of collection of coll of coll
##
DeclareCategoryCollections( "IsCyclotomic" );
DeclareCategoryCollections( "IsCyclotomicCollection" );
DeclareCategoryCollections( "IsCyclotomicCollColl" );


#############################################################################
##
#C  IsRat( <obj> )
##
##  Every rational number lies in the category `IsRat',
##  which is a subcategory of `IsCyc' (see~"Cyclotomics").
##
DeclareCategoryKernel( "IsRat", IsCyc, IS_RAT );


#############################################################################
##
#C  IsInt( <obj> )
##
##  Every rational integer lies in the category `IsInt',
##  which is a subcategory of `IsRat' (see~"Rationals").
##
DeclareCategoryKernel( "IsInt", IsRat, IS_INT );


#############################################################################
##
#C  IsPosRat( <obj> )
##
##  Every positive rational number lies in the category `IsPosRat'.
##
DeclareCategory( "IsPosRat", IsRat );


#############################################################################
##
#C  IsPosInt( <obj> )
##
##  Every positive integer lies in the category `IsPosInt'.
## 
DeclareSynonym( "IsPosInt", IsInt and IsPosRat );


#############################################################################
##
#C  IsNegRat( <obj> )
##
##  Every negative rational number lies in the category `IsNegRat'.
##
DeclareCategory( "IsNegRat", IsRat );


#############################################################################
##
#C  IsZeroCyc( <obj> )
##
##  Only the zero `0' of the cyclotomics lies in the category `IsZeroCyc'.
##
DeclareCategory( "IsZeroCyc", IsInt );


#############################################################################
##

#V  CyclotomicsFamily . . . . . . . . . . . . . . . . . family of cyclotomics
##
BIND_GLOBAL( "CyclotomicsFamily",
    NewFamily( "CyclotomicsFamily", IsCyclotomic ) );


#############################################################################
##

#R  IsSmallIntRep . . . . . . . . . . . . . . . . . .  small internal integer
##
DeclareRepresentation( "IsSmallIntRep", IsInternalRep, [] );


#############################################################################
##
#V  TYPE_INT_SMALL_ZERO . . . . . . . . . . . . . . type of the internal zero
##
BIND_GLOBAL( "TYPE_INT_SMALL_ZERO", NewType( CyclotomicsFamily,
                            IsInt and IsZeroCyc and IsSmallIntRep ) );


#############################################################################
##
#V  TYPE_INT_SMALL_NEG  . . . . . . type of a small negative internal integer
##
BIND_GLOBAL( "TYPE_INT_SMALL_NEG", NewType( CyclotomicsFamily,
                            IsInt and IsNegRat and IsSmallIntRep ) );


#############################################################################
##
#V  TYPE_INT_SMALL_POS  . . . . . . type of a small positive internal integer
##
BIND_GLOBAL( "TYPE_INT_SMALL_POS", NewType( CyclotomicsFamily,
                            IsPosInt and IsSmallIntRep ) );


#############################################################################
##
#V  TYPE_INT_LARGE_NEG  . . . . . . type of a large negative internal integer
##
BIND_GLOBAL( "TYPE_INT_LARGE_NEG", NewType( CyclotomicsFamily,
                            IsInt and IsNegRat and IsInternalRep ) );


#############################################################################
##
#V  TYPE_INT_LARGE_POS  . . . . . . type of a large positive internal integer
##
BIND_GLOBAL( "TYPE_INT_LARGE_POS", NewType( CyclotomicsFamily,
                            IsPosInt and IsInternalRep ) );


#############################################################################
##
#V  TYPE_RAT_NEG  . . . . . . . . . . .  type of a negative internal rational
##
BIND_GLOBAL( "TYPE_RAT_NEG", NewType( CyclotomicsFamily,
                            IsRat and IsNegRat and IsInternalRep ) );


#############################################################################
##
#V  TYPE_RAT_POS  . . . . . . . . . . .  type of a positive internal rational
##
BIND_GLOBAL( "TYPE_RAT_POS", NewType( CyclotomicsFamily,
                            IsRat and IsPosRat and IsInternalRep ) );

#############################################################################
##
#V  TYPE_CYC  . . . . . . . . . . . . . . . . type of an internal cyclotomics
##
BIND_GLOBAL( "TYPE_CYC",
    NewType( CyclotomicsFamily, IsCyc and IsInternalRep ) );


#############################################################################
##
#v  One( CyclotomicsFamily )
##
SetOne( CyclotomicsFamily, 1 );


#############################################################################
##
#v  Zero( CyclotomicsFamily )
##
SetZero( CyclotomicsFamily, 0 );


#############################################################################
##
#v  Characteristic( CyclotomicsFamily )
##
SetCharacteristic( CyclotomicsFamily, 0 );


#############################################################################
##
#v  IsUFDFamily( CyclotomicsFamily )
##
SetIsUFDFamily( CyclotomicsFamily, true );


#############################################################################
##
#F  E( <n> )
##
##  `E' returns the primitive <n>-th root of unity $e_n = e^{2\pi i/n}$.
##  Cyclotomics are usually entered as sums of roots of unity,
##  with rational coefficients,
##  and irrational cyclotomics are displayed in such a way.
##  (For special cyclotomics, see~"ATLAS irrationalities".)
##

# DeclareGlobalFunction( "E" );


#############################################################################
##

#C  IsInfinity( <obj> ) . . . . . . . . . . . . . . . .  category of infinity
#V  infinity  . . . . . . . . . . . . . . . . . . . . . .  the value infinity
##
##  `infinity' is a special {\GAP} object that lies in `CyclotomicsFamily'.
##  It is larger than all other objects in this family.
##  `infinity' is mainly used as return value of operations such as `Size'
##  and `Dimension' for infinite resp.~infinite dimensional domains.
##
##  Note that *no* arithmetic operations are provided for `infinity',
##  in particular there is no problem to define what `0 * infinity' or
##  `infinity - infinity' means.
##
##  Often it is useful to distinguish `infinity' from ``proper''
##  cyclotomics.
##  For that, `infinity' lies in the category `IsInfinity' but not in
##  `IsCyc', and the other cyclotomics lie in the category `IsCyc' but not
##  in `IsInfinity'.
##
DeclareCategory( "IsInfinity", IsCyclotomic );

UNBIND_GLOBAL( "infinity" );
BIND_GLOBAL( "infinity",
    Objectify( NewType( CyclotomicsFamily, IsInfinity
                        and IsPositionalObjectRep ), rec() ) );

InstallMethod( PrintObj,
    "for infinity",
    true, [ IsInfinity ], 0, function(obj) Print("infinity"); end );

InstallMethod( \=,
    "for cyclotomic and `infinity'",
    IsIdenticalObj, [ IsCyc, IsInfinity ], 0, ReturnFalse );

InstallMethod( \=,
    "for `infinity' and cyclotomic",
    IsIdenticalObj, [ IsInfinity, IsCyc ], 0, ReturnFalse );

InstallMethod( \=,
    "for `infinity' and `infinity'",
    IsIdenticalObj, [ IsInfinity, IsInfinity ], 0, ReturnTrue );

InstallMethod( \<,
    "for cyclotomic and `infinity'",
    IsIdenticalObj, [ IsCyc, IsInfinity ], 0, ReturnTrue );

InstallMethod( \<,
    "for `infinity' and cyclotomic",
    IsIdenticalObj, [ IsInfinity, IsCyc ], 0, ReturnFalse );

InstallMethod( \<,
    "for `infinity' and `infinity'",
    IsIdenticalObj, [ IsInfinity, IsInfinity ], 0, ReturnFalse );


#############################################################################
##
#P  IsIntegralCyclotomic( <obj> ) . . . . . . . . . . .  integral cyclotomics
##
##  A cyclotomic is called *integral* or *cyclotomic integer* if all
##  coefficients of its minimal polynomial over the rationals are integers.
##  Since the underlying basis of the external representation of cyclotomics
##  is an integral basis (see~"Integral Bases for Abelian Number Fields"),
##  the subring of cyclotomic integers in a cyclotomic field is formed
##  by those cyclotomics for which the external representation is a list of
##  integers.
##  For example, square roots of integers are cyclotomic integers
##  (see~"ATLAS irrationalities"), any root of unity is a cyclotomic integer,
##  character values are always cyclotomic integers,
##  but all rationals which are not integers are not cyclotomic integers.
##  
DeclareProperty( "IsIntegralCyclotomic", IsObject );

DeclareSynonym( "IsCycInt", IsIntegralCyclotomic );

InstallMethod( IsIntegralCyclotomic,
    "for an internal object",
    true,
    [ IsInternalRep ], 0,
    IS_CYC_INT );


#############################################################################
##
#A  Conductor( <cyc> )
#A  Conductor( <F> )
#A  Conductor( <list> )
##
##  For an element <cyc> of a cyclotomic field, `Conductor' returns the
##  smallest integer $n$ such that <cyc> is contained in the $n$-th
##  cyclotomic field.
##  For a field <F> or a list <list> of cyclotomics, `Conductor' returns the
##  smallest integer $n$ such that all elements of <F> resp.~all entries in
##  <list> are contained in the $n$-th cyclotomic field.
##
DeclareAttributeKernel( "Conductor", IsCyc, CONDUCTOR );


#############################################################################
##
#O  GaloisCyc( <cyc>, <k> ) . . . . . . . . . . . . . . . .  Galois conjugate
##
##  returns the cyclotomic obtained by raising the roots of unity in the
##  representation of the cyclotomic <cyc> to the <k>-th power.
##  If <k> is a fixed integer coprime to the integer $n$,
##  `GaloisCyc( ., <k> )' acts as a Galois automorphism of the $n$-th
##  cyclotomic field (see~"GaloisGroup for Number Fields");
##  to get the Galois automorphisms themselves,
##  use `GaloisGroup' (see~"GaloisGroup").
##
##  The *complex conjugate* of <cyc> is `GaloisCyc( <cyc>, -1 )',
##  which can also be computed using `ComplexConjugate'
##  (see "ComplexConjugate").
##
DeclareOperationKernel( "GaloisCyc", [ IsCyc, IsInt ], GALOIS_CYC );


#############################################################################
##
#F  NumeratorRat( <rat> ) . . . . . . . . . .  numerator of internal rational
##
##  `NumeratorRat' returns the numerator of the rational <rat>.
##  Because the numerator holds the sign of the rational it may be any
##  integer.
##  Integers are rationals with denominator $1$, thus `NumeratorRat' is the
##  identity function for integers.
##
BIND_GLOBAL( "NumeratorRat", NUMERATOR_RAT );


#############################################################################
##
#F  DenominatorRat( <rat> ) . . . . . . . .  denominator of internal rational
##
##  `DenominatorRat' returns the denominator of the rational <rat>.
##  Because the numerator holds the  sign of the rational the denominator is
##  always a positive integer.
##  Integers are rationals with the denominator 1, thus `DenominatorRat'
##  returns 1 for integers.
##
BIND_GLOBAL( "DenominatorRat", DENOMINATOR_RAT );


#############################################################################
##
#F  QuoInt( <n>, <m> )  . . . . . . . . . . . . quotient of internal integers
##
##  `QuoInt' returns the integer part of the quotient of its integer
##  operands.
##
##  If <n> and <m> are positive `QuoInt( <n>, <m> )' is the largest
##  positive integer <q> such that $<q> \* <m> \le <n>$.
##  If <n> or <m> or both are negative the absolute value of the integer part
##  of the quotient is the quotient of the absolute values of <n> and <m>,
##  and the sign of it is the product of the signs of <n> and <m>.
##
##  `QuoInt' is used in a method for the general operation
##  `EuclideanQuotient' (see~"EuclideanQuotient").
##

#DeclareGlobalFunction( "QuoInt" );
BIND_GLOBAL( "QuoInt", QUO_INT );


#############################################################################
##
#F  RemInt( <n>, <m> )  . . . . . . . . . . .  remainder of internal integers
##
##  `RemInt' returns the remainder of its two integer operands.
##
##  If <m> is not equal to zero
##  `RemInt( <n>, <m> ) = <n> - <m> * QuoInt( <n>, <m> )'.
##  Note that the rules given for `QuoInt' imply that `RemInt( <n>, <m> )'
##  has the same sign as <n> and its absolute value is strictly less than the
##  absolute value of <m>.
##  Note also that `RemInt( <n>, <m> ) = <n> mod <m>' when both <n> and <m>
##  are nonnegative.
##  Dividing by 0 signals an error.
##
##  `RemInt' is used in a method for the general operation
##  `EuclideanRemainder' (see~"EuclideanRemainder").
##

#DeclareGlobalFunction( "RemInt" );
BIND_GLOBAL( "RemInt", REM_INT );


#############################################################################
##
#F  GcdInt( <a>, <b> )  . . . . . . . . . . . . . .  gcd of internal integers
##
##  `GcdInt' returns the greatest common divisor of its two integer operands.
##
##  `GcdInt' is a method used by the general function `Gcd' (see~"Gcd").
##

#DeclareGlobalFunction( "GcdInt" );
BIND_GLOBAL( "GcdInt", GCD_INT );


#############################################################################
##
#m  Order( <cyc> ) . . . . . . . . . . . . . . . . .  order of an alg. number
##
InstallMethod( Order,
    "for a cyclotomic",
    true,
    [ IsCyc ], 0,
    function ( cyc )
    local ord, val;
    if cyc = 0 then
      Error( "argument must be nonzero" );
    elif cyc * GaloisCyc( cyc, -1 ) <> 1 then   # not a root of unity
      return infinity;
    else
      ord:= 1;
      val:= cyc;
      while val <> 1 do
        val:= val * cyc;
        ord:= ord + 1;
      od;
      return ord;
#T improve!
    fi;
    end );


#############################################################################
##
#M  Int( <int> )  . . . . . . . . . . . . . . . . . . . . . .  for an integer
#M  Int( <rat> ) . . . . . . . . . . . .   convert a rational into an integer
#M  Int( <cyc> )  . . . . . . . . . . . . .  cyclotomic integer near to <cyc>
##
InstallMethod( Int,
    "for an integer",
    true,
    [ IsInt ], 0,
    IdFunc );

InstallMethod( Int,
    "for a rational",
    true,
    [ IsRat ], 0,
    obj -> QuoInt( NumeratorRat( obj ), DenominatorRat( obj ) ) );

InstallMethod( Int,
    "for a cyclotomic",
    true,
    [ IsCyc ], 0,
    function ( x )
    local i, int, n, cfs;
    n:= Conductor( x );
    cfs:= COEFFS_CYC( x );
    int:= 0;
    for i in [ 1 .. n ] do
      int:= int + Int( cfs[i] ) * E(n)^(i-1);
    od;
    return int;
    end );


#############################################################################
##
#M  String( <int> ) . . . . . . . . . . . . . . . . . . . . .  for an integer
#M  String( <rat> ) . . . . . . . . . . . .  convert a rational into a string
#M  String( <cyc> ) . . . . . . . . . . . .  convert cyclotomic into a string
#M  String( <infinity> )  . . . . . . . . . . . . . . . . . .  for `infinity'
##
InstallMethod( String,
    "for an integer",
    true,
    [ IsInt ], 0,
    STRING_INT );

InstallMethod( String,
    "for a rational",
    true,
    [ IsRat ], 0,
    function ( rat )
    local   str;

    str := String( NumeratorRat( rat ) );
    if DenominatorRat( rat ) <> 1  then
        str := Concatenation( str, "/", String( DenominatorRat( rat ) ) );
    fi;
    ConvertToStringRep( str );
    return str;
    end );

InstallMethod( String,
    "for a cyclotomic",
    true,
    [ IsCyc ], 0,
    function( cyc )
    local i, j, En, coeffs, str;

    # get the coefficients
    coeffs := COEFFS_CYC( cyc );

    # get the root as a string
    En := Concatenation( "E(", String( Length( coeffs ) ), ")" );

    # print the first non zero coefficient
    i := 1;
    while coeffs[i] = 0 do i:= i+1; od;
    if i = 1  then
        str := ShallowCopy( String( coeffs[1] ) );
    elif coeffs[i] = -1 then
        str := Concatenation( "-", En );
    elif coeffs[i] = 1 then
        str := ShallowCopy( En );
    else
        str := Concatenation( String( coeffs[i] ), "*", En );
    fi;
    if 2 < i  then
        Add( str, '^' );
        Append( str, String(i-1) );
    fi;

    # print the other coefficients
    for j  in [i+1..Length(coeffs)]  do
        if   coeffs[j] = 1 then
            Add( str, '+' );
            Append( str, En );
        elif coeffs[j] = -1 then
            Add( str, '-' );
            Append( str, En );
        elif 0 < coeffs[j] then
            Add( str, '+' );
            Append( str, String( coeffs[j] ) );
            Add( str, '*' );
            Append( str, En );
        elif coeffs[j] < 0 then
            Append( str, String( coeffs[j] ) );
            Add( str, '*' );
            Append( str, En );
        fi;
        if 2 < j  and coeffs[j] <> 0  then
            Add( str, '^' );
            Append( str, String( j-1 ) );
        fi;
    od;

    # Convert to string representation.
    ConvertToStringRep( str );

    # Return the string.
    return str;
    end );

InstallMethod( String,
    "for infinity",
    true,
    [ IsInfinity ], 0,
    x -> "infinity" );


#############################################################################
##

#E  cyclotom.g	. . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##


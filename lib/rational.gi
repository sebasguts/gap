#############################################################################
##
#W  rational.gi                 GAP library                  Martin Schoenert
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains methods for rationals.
##
Revision.rational_gi :=
    "@(#)$Id$";


#############################################################################
##
#V  Rationals . . . . . . . . . . . . . . . . . . . . . .  field of rationals
##
InstallValue( Rationals, Objectify( NewType(
    CollectionsFamily( CyclotomicsFamily ),
    IsRationals ), rec() ) );
SetName( Rationals, "Rationals" );
SetLeftActingDomain( Rationals, Rationals );
SetIsPrimeField( Rationals, true );
SetIsCyclotomicField( Rationals, true );
SetSize( Rationals, infinity );
SetConductor( Rationals, 1 );
SetDimension( Rationals, 1 );
SetGaloisStabilizer( Rationals, [ 1 ] );
SetGeneratorsOfLeftModule( Rationals, [ 1 ] );
SetIsWholeFamily( Rationals, false );
#T necessary?
#T     automorphisms               := [ e -> e ],


#############################################################################
##
#V  GaussianRationals . . . . . . . . . . . . . . field of Gaussian rationals
##
InstallValue( GaussianRationals, Objectify( NewType(
    CollectionsFamily( CyclotomicsFamily ),
    IsGaussianRationals ), rec() ) );
SetName( GaussianRationals, "GaussianRationals" );
SetLeftActingDomain( GaussianRationals, Rationals );
SetIsPrimeField( GaussianRationals, false );
SetIsCyclotomicField( GaussianRationals, true );
SetSize( GaussianRationals, infinity );
SetConductor( GaussianRationals, 4 );
SetDimension( GaussianRationals, 2 );
SetDegreeOverPrimeField( GaussianRationals, 2 );
SetGaloisStabilizer( GaussianRationals, [ 1 ] );
SetGeneratorsOfLeftModule( GaussianRationals, [ 1, E(4) ] );
SetIsWholeFamily( GaussianRationals, false );


#############################################################################
##
#M  \in( <x>, <Rationals> ) . . . . . . . . . . membership test for rationals
##
InstallMethod( \in, true, [ IsObject, IsRationals ], 0,
    function ( x, Rationals ) return IsRat( x ); end );


#############################################################################
##
#M  Random( Rationals ) . . . . . . . . . . . . . . . . . . . random rational
##
InstallMethod( Random, true, [ IsRationals ], 0,
    function( Rationals )
    local den;
    repeat den := Random( Integers ); until den <> 0;
    return Random( Integers ) / den;
    end );


#############################################################################
##
#M  Conjugates( Rationals, <x> )  . . . . . . . . .  conjugates of a rational
##
InstallMethod( Conjugates, IsCollsElms, [ IsRationals, IsRat ], 0,
    function ( Rationals, x ) return [ x ]; end );


#############################################################################
##
#R  IsCanonicalBasisRationals
##
DeclareRepresentation( "IsCanonicalBasisRationals",
    IsAttributeStoringRep,
    [] );
#T is this needed at all?


#############################################################################
##
#M  CanonicalBasis( Rationals )
##
InstallMethod( CanonicalBasis,
    "method for Rationals",
    true, [ IsRationals ], 0,
    function( Rationals )
    local B;
    B:= Objectify( NewType( FamilyObj( Rationals ),
                                IsBasis
                            and IsCanonicalBasis
                            and IsCanonicalBasisRationals ),
                   rec() );
    SetUnderlyingLeftModule( B, Rationals );
    SetBasisVectors( B, [ 1 ] );
    end );

InstallMethod( Coefficients,
    "method for canonical basis of Rationals",
    IsCollsElms,
    [ IsBasis and IsCanonicalBasis and IsCanonicalBasisRationals,
      IsVector ], 0,
    function( B, v )
    if IsRat( v ) then
      return [ v ];
    else
      return fail;
    fi;
    end );


#T ############################################################################
#T ##
#T #M  Denominator( <rat> )
#T #M  Numerator( <rat> )
#T ##
#T InstallMethod( Denominator, true, [ IsRat ], 0, DenominatorRat );
#T InstallMethod( Numerator, true, [ IsRat ], 0, NumeratorRat );


############################################################################
##
#R  IsRationalsIteratorRep
##
DeclareRepresentation( "IsRationalsIteratorRep", IsComponentObjectRep,
    [ "structure", "actualn", "up", "sign", "pos", "coprime", "len" ] );


############################################################################
##
#M  Iterator( Rationals )
##
##  Let $A_n = \{ \frac{p}{q} ; p,q \in\{ 1, \ldots, n \} \}$
##      $B_n = A_n \setminus \bigcup_{i<n} A_i$,
##      $B_0 = \{ 0 \}$, and
##      $B_{-n} = \{ -x; x\in B_n \}$ for $n \in\N$.
##  Then $\Q = \bigcup_{n\in\Z} B_n$ as a disjoint union.
##
##  $\|B_n\| = 2 ( n - 1 ) - 2 ( \tau(n) - 2 ) = 2 ( n - \tau(n) + 1 )$
##  where $\tau(n)$ denotes the number of divisors of $n$.
##  Now define the ordering on $\Q$ by the ordering of the sets $B_n$
##  as defined in 'IntegersOps.Iterator', by the natural ordering of
##  elements in each $B_n$ for positive $n$, and the reverse of this
##  ordering for negative $n$.
##
InstallMethod( Iterator,
    "for `Rationals'",
    true,
    [ IsRationals ], 0,
    function( Rationals )
    return Objectify( NewType( IteratorsFamily,
                                   IsIterator
                               and IsMutable
                               and IsRationalsIteratorRep ),
                      rec(
                           structure := Rationals,
                           actualn   := 0,
                           up        := false,
                           sign      := -1,
                           pos       := 1,
                           coprime   := [ 1 ],
                           len       := 1       ) );
    end );

InstallMethod( IsDoneIterator,
    "for iterator of `Rationals'",
    true,
    [ IsIterator and IsRationalsIteratorRep ], 0,
    ReturnFalse );

InstallMethod( ShallowCopy,
    "for iterator of `Rationals'",
    true,
    [ IsIterator and IsRationalsIteratorRep ], 0,
    iter -> Objectify( Subtype( TypeObj( iter ), IsMutable ),
                       rec(
                            structure := Rationals,
                            actualn   := iter!.actualn,
                            up        := iter!.up,
                            sign      := iter!.sign,
                            pos       := iter!.pos,
                            coprime   := ShallowCopy( iter!.coprime ),
                            len       := Length( iter!.coprime ) ) ) );

InstallMethod( NextIterator,
    "for mutable iterator of `Rationals'",
    true,
    [ IsIterator and IsMutable and IsRationalsIteratorRep ], 0,
    function( iter )

    local value;

    if iter!.actualn = 1 then

      # Catch the special case that numerator and denominator are
      # allowed to be equal.
      value:= iter!.sign;
      if iter!.sign = -1 then
        iter!.actualn := 2;
        iter!.len     := 1;
        iter!.pos     := 1;
        iter!.coprime := [ 1 ];
      fi;
      iter!.sign:= - iter!.sign;

    elif iter!.up then

      # We are in the first half (proper fractions).
      value:= iter!.sign * iter!.coprime[ iter!.pos ] / iter!.actualn;

      # Check whether we reached the last element of the first half.
      if iter!.pos = iter!.len then
        iter!.up:= false;
      else
        iter!.pos:= iter!.pos + 1;
      fi;

    else

      # We are in the second half.
      value:= iter!.sign * iter!.actualn / iter!.coprime[ iter!.pos ];

      # Check whether we reached the last element of the second half.
      if iter!.pos = 1 then
        if iter!.sign = -1 then
          iter!.actualn := iter!.actualn + 1;
          iter!.coprime := PrimeResidues( iter!.actualn );
          iter!.len     := Length( iter!.coprime );
        fi;
        iter!.sign := - iter!.sign;
        iter!.up   := true;
      else
        iter!.pos:= iter!.pos - 1;
      fi;

    fi;

    return value;
    end );


#############################################################################
##
#R  IsRationalsEnumerator
##
DeclareRepresentation( "IsRationalsEnumerator",
    IsDomainEnumerator and IsAttributeStoringRep, [] );


#############################################################################
##
#M  Enumerator( Rationals )
##
InstallMethod( Enumerator, true, [ IsRationals ], 0,
    function( Rationals )
    local enum;
    enum:= Objectify( NewType( FamilyObj( Rationals ),
                               IsRationalsEnumerator ),
                      rec() );
    SetUnderlyingCollection( enum, Rationals );
    return enum;
    end );

InstallMethod( Position, true,
    [ IsRationalsEnumerator, IsCyc, IsZeroCyc ], 0,
    function( enum, elm, zero )

    local num,
          den,
          max,
          number,
          residues;

    if not IsRat(elm)  then
        return fail;
    fi;
    num:= NumeratorRat( elm);
    den:= DenominatorRat( elm );
    max:= AbsInt( num );
    if max < den then
      max:= den;
    fi;

    if   elm =  0 then
      number:= 1;
    elif elm =  1 then
      number:= 2;
    elif elm = -1 then
      number:= 3;
    else

      # Take the sum over all inner squares.
      # For $i > 1$, the positive half of the $i$-th square has
      # $n_i = 2 \varphi(i)$ elements, $n_1 = 1$, so the sum is
      # \[ 1 + \sum_{j=1}^{max-1} 2 n_j =
      #    4 \sum_{j=1}^{max-1} \varphi(j) - 1 . \]
      number:= 4 * Sum( [ 1 .. max-1 ], Phi ) - 1;

      # Add the part in the actual square.
      residues:= PrimeResidues( max );
      if num < 0 then
        # Add $n_{max}$.
        number:= number + 2 * Length( residues );
        num:= - num;
      fi;
      if num > den then
        number:= number + 2 * Length( residues )
                 - Position( residues, den ) + 1;
      else
        number:= number + Position( residues, num );
      fi;

    fi;

    # Return result.
    return number;
    end );

InstallMethod( \[\], true, [ IsRationalsEnumerator, IsPosInt ], 0,
    function( enum, number )

    local elm,
          max,
          4phi,
          sign;

    if number <= 3 then

      if   number = 1 then
        elm:=  0;
      elif number = 2 then
        elm:=  1;
      else
        elm:= -1;
      fi;

    else

      # Compute the maximum of numerator and denominator,
      # and subtract the number of inner sqares from 'number'.

      number:= number - 3;

      max:= 2;
      4phi:= 4 * Phi( max );
      while number > 4phi do
        number := number - 4phi;
        max    := max + 1;
        4phi   := 4 * Phi( max );
      od;
      if number > 4phi / 2 then
        sign:= -1;
        number:= number - 4phi / 2;
      else
        sign:= 1;
      fi;
      if number > 4phi / 4 then
        elm:= sign * max / PrimeResidues( max )[ 4phi / 2 - number + 1 ];
      else
        elm:= sign * PrimeResidues( max )[ number ] / max;
      fi;

    fi;

    return elm;
    end );


#############################################################################
##
#F  EvalF(<number>) . . . . . .  floating point evaluation of rational number
##
BindGlobal( "EvalF", function(arg)
local r,f,i,s;
  r:=arg[1];
  if r<0 then
    r:=-r;
    s:=['-'];
  else
    s:=[];
  fi;
  if Length(arg)>1 then 
    f:=arg[2];
  else
    f:=10;
  fi;
  i:=Int(r);
  s:=Concatenation(s,String(i));
  if r<>i then
    Add(s,'.');
    r:=String(Int((r-i)*10^f));
    while Length(r)<f do
      Add(s,'0');
      f:=f-1;
    od;
    s:=Concatenation(s,String(r));
  fi;
  IsString(s);
  return s;
end );


#############################################################################
##
#M  RoundCyc( <cyc> ) . . . . . . . . . . cyclotomic integer near to <cyc>
##
InstallMethod( RoundCyc, "Rational", true, [ IsRat],
        0,  function ( r )

    if r < 0  then
        return Int( r - 1 / 2 );
    else
        return Int( r + 1 / 2 );
    fi;

end );

#############################################################################
##
#E


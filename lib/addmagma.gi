#############################################################################
##
#W  addmagma.gi                 GAP library                     Thomas Breuer
##
#W  @(#)$Id$
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.addmagma_gi :=
    "@(#)$Id$";


#############################################################################
##
#M  Print( <A> )  . . . . . . . . . . . . . . . . . . print an additive magma
##
InstallMethod( PrintObj,
    "for an add. magma",
    true,
    [ IsAdditiveMagma ], 0,
    function( A )
    Print( "AdditiveMagma( ... )" );
    end );

InstallMethod( PrintObj,
    "for an add. magma with generators",
    true,
    [ IsAdditiveMagma and HasGeneratorsOfAdditiveMagma ], 0,
    function( A )
    Print( "AdditiveMagma( ", GeneratorsOfAdditiveMagma( A ), " )" );
    end );

InstallMethod( PrintObj,
    "for an add. magma-with-zero with generators",
    true,
    [ IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagmaWithZero ], 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveMagmaWithZero( A ) ) then
      Print( "AdditiveMagmaWithZero( ", Zero( A ), " )" );
    else
      Print( "AdditiveMagmaWithZero( ",
             GeneratorsOfAdditiveMagmaWithZero( A ), " )" );
    fi;
    end );

InstallMethod( PrintObj,
    "for an add. magma-with-inverses with generators",
    true,
    [     IsAdditiveGroup
      and HasGeneratorsOfAdditiveGroup ], 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveGroup( A ) ) then
      Print( "AdditiveGroup( ", Zero( A ), " )" );
    else
      Print( "AdditiveGroup( ",
             GeneratorsOfAdditiveGroup( A ), " )" );
    fi;
    end );


#############################################################################
##
#M  ViewObj( <A> )  . . . . . . . . . . . . . . . . . . .  view an add. magma
##
InstallMethod( ViewObj,
    "for an add. magma",
    true,
    [ IsAdditiveMagma ], 0,
    function( A )
    Print( "<additive magma>" );
    end );

InstallMethod( ViewObj,
    "for an add. magma with generators",
    true,
    [ IsAdditiveMagma and HasGeneratorsOfAdditiveMagma ], 0,
    function( A )
    Print( "<additive magma with ",
           Length( GeneratorsOfAdditiveMagma( A ) ), " generators>" );
    end );

InstallMethod( ViewObj,
    "for an add. magma-with-zero with generators",
    true,
    [ IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagmaWithZero ], 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveMagmaWithZero( A ) ) then
      Print( "<trivial additive magma-with-zero>" );
    else
      Print( "<additive magma-with-zero with ",
             Length( GeneratorsOfAdditiveMagmaWithZero( A ) ),
             " generators>" );
    fi;
    end );

InstallMethod( ViewObj,
    "for an add. magma-with-inverses with generators",
    true,
    [     IsAdditiveGroup
      and HasGeneratorsOfAdditiveGroup ], 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveGroup( A ) ) then
      Print( "<trivial additive magma-with-inverses>" );
    else
      Print( "<additive magma-with-inverses with ",
             Length( GeneratorsOfAdditiveGroup( A ) ),
             " generators>" );
    fi;
    end );


#############################################################################
##
#M  IsTrivial( <A> )  . . . . . . . test whether an additive magma is trivial
##
InstallImmediateMethod( IsTrivial,
    IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagmaWithZero , 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveMagmaWithZero( A ) ) then
      return true;
    else
      TryNextMethod();
    fi;
    end );

InstallImmediateMethod( IsTrivial,
    IsAdditiveGroup
    and HasGeneratorsOfAdditiveGroup, 0,
    function( A )
    if IsEmpty( GeneratorsOfAdditiveGroup( A ) ) then
      return true;
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#F  AdditiveMagma( <gens> )
#F  AdditiveMagma( <Fam>, <gens> )
##
InstallGlobalFunction( AdditiveMagma, function( arg )

    # list of generators
    if Length( arg ) = 1 and IsList( arg[1] ) and 0 < Length( arg[1] ) then
      return AdditiveMagmaByGenerators( arg[1] );

    # family plus list of generators
    elif Length( arg ) = 2 and IsFamily( arg[1] ) and IsList( arg[1] ) then
      return AdditiveMagmaByGenerators( arg[1], arg[2] );

    # generators
    elif 0 < Length( arg ) then
      return AdditiveMagmaByGenerators( arg );
    fi;

    # no argument given, error
    Error("usage: AdditiveMagma(<gens>), AdditiveMagma(<Fam>,<gens>)");

end );


#############################################################################
##
#F  SubadditiveMagma( <M>, <gens> )  add. submagma of <M> generated by <gens>
##
InstallGlobalFunction( SubadditiveMagma, function( M, gens )

    if not IsAdditiveMagma( M ) then
        Error( "<M> must be an additive magma" );
    elif IsEmpty( gens ) then
        return SubadditiveMagmaNC( M, gens );
    elif not IsHomogeneousList(gens)  then
        Error( "<gens> must be a homogeneous list of elements" );
    elif not IsIdenticalObj( FamilyObj(M), FamilyObj(gens) )  then
        Error( "families of <gens> and <M> are different" );
    fi;
    if not ForAll( gens, x -> x in M ) then
        Error( "<gens> must be elements in <M>" );
    fi;
    return SubadditiveMagmaNC( M, gens );

end );


#############################################################################
##
#F  SubadditiveMagmaNC( <M>, <gens> )
##
##  Note that `SubadditiveMagmaNC' is allowed to call `Objectify'
##  in the case that <gens> is empty.
##
InstallGlobalFunction( SubadditiveMagmaNC, function( M, gens )
    local K, S;

    if IsEmpty( gens ) then
      K:= NewType( FamilyObj(M),
                       IsAdditiveMagma
                   and IsTrivial
                   and IsAttributeStoringRep );
      S:= Objectify( K, rec() );
      SetGeneratorsOfAdditiveMagma( S, [] );
    else
      S:= AdditiveMagmaByGenerators(gens);
    fi;
    SetParent( S, M );
    return S;

end );


#############################################################################
##
#F  AdditiveMagmaWithZero( <gens> )
#F  AdditiveMagmaWithZero( <Fam>, <gens> )
##
InstallGlobalFunction( AdditiveMagmaWithZero, function( arg )

    # list of generators
    if Length( arg ) = 1 and IsList( arg[1] ) and 0 < Length( arg[1] ) then
      return AdditiveMagmaWithZeroByGenerators( arg[1] );

    # family plus list of generators
    elif Length( arg ) = 2 and IsFamily( arg[1] ) and IsList( arg[1] ) then
      return AdditiveMagmaWithZeroByGenerators( arg[1], arg[2] );

    # generators
    elif 0 < Length( arg ) then
      return AdditiveMagmaWithZeroByGenerators( arg );
    fi;

    # no argument given, error
    Error("usage: AdditiveMagmaWithZero(<gens>), ",
          "AdditiveMagmaWithZero(<Fam>,<gens>)");

end );


#############################################################################
##
#F  SubadditiveMagmaWithZero( <M>, <gens> )
#F                        . . .  add. submagma-with-one of <M> gen. by <gens>
##
InstallGlobalFunction( SubadditiveMagmaWithZero, function( M, gens )
    if not IsAdditiveMagmaWithZero( M ) then
        Error( "<M> must be an additive magma-with-zero" );
    elif IsEmpty( gens ) then
        return SubadditiveMagmaWithZeroNC( M, gens );
    elif not IsHomogeneousList(gens)  then
        Error( "<gens> must be a homogeneous list of elements" );
    elif not IsIdenticalObj( FamilyObj(M), FamilyObj(gens) )  then
        Error( "families of <gens> and <M> are different" );
    fi;
    if not ForAll( gens, x -> x in M ) then
        Error( "<gens> must be elements in <M>" );
    fi;
    return SubadditiveMagmaWithZeroNC( M, gens );
end );


#############################################################################
##
#F  SubadditiveMagmaWithZeroNC( <M>, <gens> )
##
##  Note that `SubadditiveMagmaWithZeroNC' is allowed to call `Objectify'
##  in the case that <gens> is empty.
##
##  Furthermore note that a trivial additive magma with zero is automatically
##  an additive group.
##
InstallGlobalFunction( SubadditiveMagmaWithZeroNC, function( M, gens )
    local K, S;

    if IsEmpty( gens ) then
      K:= NewType( FamilyObj(M),
                       IsAdditiveGroup
                   and IsTrivial
                   and IsAttributeStoringRep );
      S:= Objectify( K, rec() );
      SetGeneratorsOfAdditiveGroup( S, [] );
    else
      S:= AdditiveMagmaWithZeroByGenerators(gens);
    fi;
    SetParent( S, M );
    return S;
end );


#############################################################################
##
#F  AdditiveGroup( <gens> )
#F  AdditiveGroup( <Fam>, <gens> )
##
InstallGlobalFunction( AdditiveGroup, function( arg )

    # list of generators
    if Length( arg ) = 1 and IsList( arg[1] ) and 0 < Length( arg[1] ) then
      return AdditiveGroupByGenerators( arg[1] );

    # family plus list of generators
    elif Length( arg ) = 2 and IsFamily( arg[1] ) and IsList( arg[1] ) then
      return AdditiveGroupByGenerators( arg[1], arg[2] );

    # generators
    elif 0 < Length( arg ) then
      return AdditiveGroupByGenerators( arg );
    fi;

    # no argument given, error
    Error("usage: AdditiveGroup(<gens>), ",
          "AdditiveGroup(<Fam>,<gens>)");

end );


#############################################################################
##
#F  SubadditiveGroup( <M>, <gens> ) . . . add. subgroup of <M> gen. by <gens>
##
InstallGlobalFunction( SubadditiveGroup, function( M, gens )
    if not IsAdditiveGroup( M ) then
        Error( "<M> must be an additive group" );
    elif IsEmpty( gens ) then
        return SubadditiveGroupNC( M, gens );
    elif not IsHomogeneousList(gens)  then
        Error( "<gens> must be a homogeneous list of elements" );
    elif not IsIdenticalObj( FamilyObj(M), FamilyObj(gens) )  then
        Error( "families of <gens> and <M> are different" );
    fi;
    if not ForAll( gens, x -> x in M ) then
        Error( "<gens> must be elements in <M>" );
    fi;
    return SubadditiveGroupNC( M, gens );
end );


#############################################################################
##
#F  SubadditiveGroupNC( <M>, <gens> )
##
##  Note that `SubadditiveGroupNC' is allowed to call `Objectify'
##  in the case that <gens> is empty.
##
InstallGlobalFunction( SubadditiveGroupNC, function( M, gens )
    local K, S;

    if IsEmpty( gens ) then
      K:= NewType( FamilyObj(M),
                       IsAdditiveGroup
                   and IsTrivial
                   and IsAttributeStoringRep );
      S:= Objectify( K, rec() );
      SetGeneratorsOfAdditiveGroup( S, [] );
    else
      S:= AdditiveGroupByGenerators(gens);
    fi;
    SetParent( S, M );
    return S;
end );


#############################################################################
##
#M  TrivialSubadditiveMagmaWithZero( <M> )  . . . for an add.-magma-with-zero
##
InstallMethod( TrivialSubadditiveMagmaWithZero,
    "for add.-magma-with-zero",
    true,
    [ IsAdditiveMagmaWithZero ], 0,
    M -> SubadditiveMagmaWithZeroNC( M, [] ) );


#############################################################################
##
#M  AdditiveMagmaByGenerators( <gens> ) . . . . . . . . . .  for a collection
##
InstallMethod( AdditiveMagmaByGenerators,
    "for collection",
    true,
    [ IsCollection ] , 0,
    function( gens )
    local M;
    M:= Objectify( NewType( FamilyObj( gens ),
                            IsAdditiveMagma and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveMagma( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  AdditiveMagmaByGenerators( <Fam>, <gens> )  . . . . . for family and list
##
InstallOtherMethod( AdditiveMagmaByGenerators,
    "for family and list",
    true,
    [ IsFamily, IsList ], 0,
    function( family, gens )
    local M;
    if not ( IsEmpty(gens) or IsIdenticalObj( FamilyObj(gens), family ) ) then
      Error( "<family> and family of <gens> do not match" );
    fi;
    M:= Objectify( NewType( family,
                            IsAdditiveMagma and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveMagma( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  AdditiveMagmaWithZeroByGenerators( <gens> ) . . . . . .  for a collection
##
InstallMethod( AdditiveMagmaWithZeroByGenerators,
    "for collection",
    true,
    [ IsCollection ] , 0,
    function( gens )
    local M;
    M:= Objectify( NewType( FamilyObj( gens ),
                       IsAdditiveMagmaWithZero and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveMagmaWithZero( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  AdditiveMagmaWithZeroByGenerators( <Fam>, <gens> )  . for family and list
##
InstallOtherMethod( AdditiveMagmaWithZeroByGenerators,
    "for family and list",
    true,
    [ IsFamily, IsList ], 0,
    function( family, gens )
    local M;
    if not ( IsEmpty(gens) or IsIdenticalObj( FamilyObj(gens), family ) ) then
      Error( "<family> and family of <gens> do not match" );
    fi;
    M:= Objectify( NewType( family,
                       IsAdditiveMagmaWithZero and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveMagmaWithZero( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  AdditiveGroupByGenerators( <gens> ) . . . .  for a collection
##
InstallMethod( AdditiveGroupByGenerators,
    "for collection",
    true,
    [ IsCollection ] , 0,
    function( gens )
    local M;
    M:= Objectify( NewType( FamilyObj( gens ),
                     IsAdditiveGroup and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveGroup( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  AdditiveGroupByGenerators(<Fam>,<gens>) . for family and list
##
InstallOtherMethod( AdditiveGroupByGenerators,
    "for family and list",
    true,
    [ IsFamily, IsList ], 0,
    function( family, gens )
    local M;
    if not ( IsEmpty(gens) or IsIdenticalObj( FamilyObj(gens), family ) ) then
      Error( "<family> and family of <gens> do not match" );
    fi;
    M:= Objectify( NewType( family,
                     IsAdditiveGroup and IsAttributeStoringRep ),
                   rec() );
    SetGeneratorsOfAdditiveGroup( M, AsList( gens ) );
    return M;
    end );


#############################################################################
##
#M  GeneratorsOfAdditiveMagma( <A> )
#M  GeneratorsOfAdditiveMagmaWithZero( <A> )
#M  GeneratorsOfAdditiveGroup( <A> )
##
##  If nothing special is known about the additive magma <A> we have
##  no chance to get the required generators.
##
##  If we know `GeneratorsOfAdditiveMagma',
##  they are also `GeneratorsOfAdditiveMagmaWithZero'.
##  If we know `GeneratorsOfAdditiveMagmaWithZero',
##  they are also `GeneratorsOfAdditiveGroup'.
##
InstallImmediateMethod( GeneratorsOfAdditiveMagmaWithZero,
    IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagma, 0,
    A -> GeneratorsOfAdditiveMagma( A ) );

InstallImmediateMethod( GeneratorsOfAdditiveGroup,
    IsAdditiveGroup and HasGeneratorsOfAdditiveMagmaWithZero, 0,
    A -> GeneratorsOfAdditiveMagmaWithZero( A ) );


InstallMethod( GeneratorsOfAdditiveMagma, true,
    [ IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagmaWithZero ], 0,
    A -> Concatenation( GeneratorsOfAdditiveMagmaWithZero( A ),
              [ Zero( A ) ] ) );

InstallMethod( GeneratorsOfAdditiveMagma, true,
    [     IsAdditiveGroup
      and HasGeneratorsOfAdditiveGroup ], 0,
    A -> Concatenation( GeneratorsOfAdditiveGroup( A ),
              [ Zero( A ) ],
              List( GeneratorsOfAdditiveGroup( A ),
                    AdditiveInverse ) ) );

InstallMethod( GeneratorsOfAdditiveMagmaWithZero, true,
    [     IsAdditiveGroup
      and HasGeneratorsOfAdditiveGroup ], 0,
    A -> Concatenation( GeneratorsOfAdditiveGroup( A ),
              List( GeneratorsOfAdditiveGroup( A ),
                    AdditiveInverse ) ) );


#############################################################################
##
#M  Representative( <A> ) . . . . . . . . .  one element of an additive magma
##
InstallMethod( Representative,
    "for additive magma with known generators",
    true,
    [ IsAdditiveMagma and HasGeneratorsOfAdditiveMagma ], 0,
    RepresentativeFromGenerators( GeneratorsOfAdditiveMagma ) );

InstallMethod( Representative,
    "for additive-magma-with-zero with known generators",
    true,
    [ IsAdditiveMagmaWithZero and HasGeneratorsOfAdditiveMagmaWithZero ], 0,
    RepresentativeFromGenerators( GeneratorsOfAdditiveMagmaWithZero ) );

InstallMethod( Representative,
    "for additive-magma-with-inverses with known generators",
    true,
    [ IsAdditiveGroup
      and HasGeneratorsOfAdditiveGroup ], 0,
    RepresentativeFromGenerators( GeneratorsOfAdditiveGroup ) );

InstallMethod( Representative,
    "for additive-magma-with-zero with known zero",
    true,
    [ IsAdditiveMagmaWithZero and HasZero ], SUM_FLAGS,
    Zero );


#############################################################################
##
#M  AdditiveNeutralElement( <A> ) . . . . . . . . . zero of an additive magma
##
InstallMethod( AdditiveNeutralElement, true, [ IsAdditiveMagma ], 0,
    function( M )
    local m;
    if IsFinite( M ) then
      for m in M do
        if ForAll( M, n -> n + m = n ) then
          return m;
        fi;
      od;
      return fail;
    else
      TryNextMethod();
    fi;
    end );


#############################################################################
##
#M  Zero( <A> ) . . . . . . . . . . . . . . . . . . zero of an additive magma
##
InstallOtherMethod( Zero,
    "for additive magma",
    true, [ IsAdditiveMagma ], 0,
    function( A )
    local zero;
    zero:= Zero( Representative( A ) );
    if zero <> fail and zero in A then
      return zero;
    else
      return fail;
    fi;
    end );

InstallOtherMethod( Zero,
    "for additive magma with zero (look at family)",
    true, [ IsAdditiveMagmaWithZero ], SUM_FLAGS,
    function( A )
    A:= ElementsFamily( FamilyObj( A ) );
    if HasZero( A ) then
      return Zero( A );
    else
      TryNextMethod();
    fi;
    end );
#T immediate?

InstallOtherMethod( Zero,
    "for an add. magma-with-zero with parent (ask the parent)",
    true,
    [ IsAdditiveMagmaWithZero and HasParent ], 0,
    A -> Zero( Parent( A ) ) );
#T really ask the parent for such information?

InstallOtherMethod( Zero,
    "for additive magma with zero",
    true,
    [ IsAdditiveMagmaWithZero ], 0,
    A -> Zero( Representative( A ) ) );


#############################################################################
##
#M  Enumerator( <A> ) . . . .  enumerator of trivial additive magma with zero
#M  EnumeratorSorted( <A> ) .  enumerator of trivial additive magma with zero
##
EnumeratorOfTrivialAdditiveMagmaWithZero := A -> Immutable( [ Zero( A ) ] );

InstallMethod( Enumerator,
    "for trivial add. magma-with-zero",
    true,
    [ IsAdditiveMagmaWithZero and IsTrivial ], 0,
    EnumeratorOfTrivialAdditiveMagmaWithZero );

InstallMethod( EnumeratorSorted,
    "for trivial add. magma-with-zero",
    true,
    [ IsAdditiveMagmaWithZero and IsTrivial ], 0,
    EnumeratorOfTrivialAdditiveMagmaWithZero );


#############################################################################
##
#F  ClosureAdditiveMagmaDefault( <A>, <elm> )  closure of add. magma with elm
##
BindGlobal( "ClosureAdditiveMagmaDefault", function( A, elm )

    local   C,          # closure `\< <a>, <obj> \>', result
            gens,       # generators of <A>
            gen,        # generator of <A> or <C>
            Celements,  # intermediate list of elements
            len;        # current number of elements

    gens:= GeneratorsOfAdditiveMagma( A );

    # try to avoid adding an element to a add. magma that already contains it
    if   elm in gens
      or ( HasAsSSortedList( A ) and elm in AsSSortedList( A ) )
    then
        return A;
    fi;

    # make the closure add. magma
    gens:= Concatenation( gens, [ elm ] );
    C:= AdditiveMagmaByGenerators( gens );
    UseSubsetRelation( C, A );

    # if the elements of <A> are known then extend this list
    # (multiply each element from the left and right with the new
    # generator, and then multiply with all elements until the
    # list becomes stable)
    if HasAsSSortedList( A ) then

        Celements := ShallowCopy( AsSSortedList( A ) );
        AddSet( Celements, elm );
        UniteSet( Celements, Celements + elm );
        UniteSet( Celements, elm + Celements );
        repeat
            len:= Length( Celements );
            for gen in Celements do
                UniteSet( Celements, Celements + gen );
                UniteSet( Celements, gen + Celements );
            od;
        until len = Length( Celements );

        SetAsSSortedList( C, AsSSortedList( Celements ) );
        SetIsFinite( C, true );
        SetSize( C, Length( Celements ) );

    fi;

    # return the closure
    return C;
end );


#############################################################################
##
#M  Enumerator( <A> ) . . . . . . . . .  set of the elements of an add. magma
#M  EnumeratorSorted( <A> ) . . . . . .  set of the elements of an add. magma
##
BindGlobal( "EnumeratorOfAdditiveMagma", function( A )

    local   gens,       # add. magma generators of <A>
            H,          # subadd. magma of the first generators of <A>
            gen;        # generator of <A>

    # handle the case of an empty add. magma
    gens:= GeneratorsOfAdditiveMagma( A );
    if IsEmpty( gens ) then
      return [];
    fi;

    # start with the empty add. magma and its element list
    H:= SubadditiveMagma( A, [] );
    SetAsSSortedList( H, Immutable( [ ] ) );

    # Add the generators one after the other.
    # We use a function that maintains the elements list for the closure.
    for gen in gens do
      H:= ClosureAdditiveMagmaDefault( H, gen );
    od;

    # return the list of elements
    Assert( 2, HasAsSSortedList( H ) );
    return AsSSortedList( H );
end );

InstallMethod( Enumerator,
    "generic method for an add. magma",
    true,
    [ IsAdditiveMagma and IsAttributeStoringRep ], 0,
    EnumeratorOfAdditiveMagma );

InstallMethod( EnumeratorSorted,
    "generic method for an add. magma",
    true,
    [ IsAdditiveMagma and IsAttributeStoringRep ], 0,
    EnumeratorOfAdditiveMagma );


#############################################################################
##
#M  IsSubset( <M>, <N> )  . . . . . . . . . . . . . . for two additive magmas
##
InstallMethod( IsSubset,
    "for two additive magmas",
    IsIdenticalObj,
    [ IsAdditiveMagma, IsAdditiveMagma ], 0,
    function( M, N )
    return IsSubset( M, GeneratorsOfAdditiveMagma( N ) );
    end );


#############################################################################
##
#M  IsSubset( <M>, <N> )  . . . . . . . . . for two additive magmas with zero
##
InstallMethod( IsSubset,
    "for two additive magmas with zero",
    IsIdenticalObj,
    [ IsAdditiveMagmaWithZero, IsAdditiveMagmaWithZero ], 0,
    function( M, N )
    return IsSubset( M, GeneratorsOfAdditiveMagmaWithZero( N ) );
    end );


#############################################################################
##
#M  IsSubset( <M>, <N> )  . . . . . . . for two additive magmas with inverses
##
InstallMethod( IsSubset,
    "for two additive magmas with inverses",
    IsIdenticalObj,
    [ IsAdditiveGroup, IsAdditiveGroup ], 0,
    function( M, N )
    return IsSubset( M, GeneratorsOfAdditiveGroup( N ) );
    end );


#############################################################################
##
#M  ClosureAdditiveGroup( <A>, <a> )  . . . . . .  for add. group and element
##
InstallMethod( ClosureAdditiveGroup,
    "for add. group and element",
    IsCollsElms,
    [ IsAdditiveGroup, IsAdditiveElement ], 0,
    function( A, a )

    # if possible test if the element lies in the add. group already
    if a in GeneratorsOfAdditiveGroup( A ) or
       ( HasAsList( A ) and a in AsList( A ) ) then
      return A;
    fi;

    # Otherwise make a new add. group.
    return AdditiveGroupByGenerators(
               Concatenation( GeneratorsOfAdditiveGroup( A ), [ a ] ) );
    end );


#############################################################################
##
#M  ClosureAdditiveGroup( <A>, <B> )  . . . . . . . . . . for two add. groups
##
InstallOtherMethod( ClosureAdditiveGroup,
    "for two add. groups",
    IsIdenticalObj,
    [ IsAdditiveGroup, IsAdditiveGroup ], 0,
    function( A, B )
    local C, b;
    C:= A;
    for b in GeneratorsOfAdditiveGroup( B ) do
      C:= ClosureAdditiveGroup( C, b );
    od;
    return C;
    end );


#############################################################################
##
#E


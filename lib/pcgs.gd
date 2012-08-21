#############################################################################
##
#W  pcgs.gd                     GAP Library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the operations for polycylic generating systems.
##
Revision.pcgs_gd :=
    "@(#)$Id$";

#############################################################################
##
#C  IsGeneralPcgs(<obj>)
##
##  The category of general pcgs. Each modulo pcgs is a general pcgs.
##  Relative orders are known for general pcgs, but it might not be
##  possible to compute exponent vectors or other elementary operations 
##  with respect to a general pcgs.
DeclareCategory( "IsGeneralPcgs",
    IsHomogeneousList and IsDuplicateFreeList and IsFinite
    and IsMultiplicativeElementWithInverseCollection );

#############################################################################
##
#C  IsModuloPcgs(<obj>)
##
##  The category of modulo pcgs. Note that each pcgs is a modulo pcgs for
##  the trivial subgroup. 
DeclareCategory("IsModuloPcgs",IsGeneralPcgs);

#############################################################################
##
#C  IsPcgs(<obj>)
##
##  The category of pcgs. 
DeclareCategory( "IsPcgs", IsModuloPcgs);


#############################################################################
##
#C  IsPcgsFamily
##
DeclareCategory(
    "IsPcgsFamily",
    IsFamily );


#############################################################################
##
#R  IsPcgsDefaultRep
##
DeclareRepresentation(
    "IsPcgsDefaultRep",
    IsComponentObjectRep and IsAttributeStoringRep, [] );


#############################################################################
##
#O  PcgsByPcSequence( <fam>, <pcs> )
#O  PcgsByPcSequenceNC( <fam>, <pcs> )
##
##  constructs a pcgs for the elements family <fam> from the elements in the
##  list <pcs>. The elements must lie in the family <fam>.
##  `PcgsByPcSequence'(`NC') will always create a new pcgs which is not
##  induced by any other pcgs.
DeclareOperation( "PcgsByPcSequence", [ IsFamily, IsList ] );
DeclareOperation( "PcgsByPcSequenceNC", [ IsFamily, IsList ] );


#############################################################################
##
#O  PcgsByPcSequenceCons( <req-filters>, <imp-filters>, <fam>, <pcs> )
##
DeclareConstructor( "PcgsByPcSequenceCons",
    [ IsObject, IsObject, IsFamily, IsList ] );


#############################################################################
##
#A  GroupByPcgs( <pcgs> )
##
DeclareAttribute(
    "GroupByPcgs",
    IsPcgs );



#############################################################################
##
#A  GroupOfPcgs( <pcgs> )
##
##  The group generated by <pcgs>.
DeclareAttribute(
    "GroupOfPcgs",
    IsPcgs );



#############################################################################
##
#A  OneOfPcgs( <pcgs> )
##
##  The identity of the group generated by <pcgs>.
DeclareAttribute(
    "OneOfPcgs",
    IsPcgs );



#############################################################################
##
#A  PcSeries( <pcgs> )
##
##  returns the subnormal series determined by <pcgs>.
DeclareAttribute( "PcSeries", IsPcgs );

#############################################################################
##
#A  IndicesNormalSteps( <pcgs> )
##
##  Let <G> be the group defined by <pcgs> and let <pcgs> = $(g_1, \ldots, 
##  g_n)$.  This function returns a sorted list of integers indicating
##  the tails of <pcgs> which generate a normal subgroup of <G>. That
##  is, whenever $(g_i, \ldots, g_n)$ is a normal subgroup of <G>,
##  then $i$ is an element of the list. In particular, the list always
##  starts with 1 and ends with n+1.
DeclareAttribute( "IndicesNormalSteps", IsPcgs );

#############################################################################
##
#A  NormalSeriesByPcgs( <pcgs> )
##
##  returns the series of all normal subgroups contained in the pc series
##  determined by <pcgs>.
DeclareAttribute( "NormalSeriesByPcgs", IsPcgs);

#############################################################################
##
#P  IsPrimeOrdersPcgs( <pcgs> )
##
##  tests whether the relative orders of <pcgs> are prime numbers. 
DeclareProperty( "IsPrimeOrdersPcgs", IsGeneralPcgs );

#############################################################################
##
#P  IsFiniteOrdersPcgs( <pcgs> )
##
##  tests whether the relative orders of <pcgs> are all finite.
DeclareProperty( "IsFiniteOrdersPcgs", IsGeneralPcgs );

#############################################################################
##
#A  RefinedPcGroup( <G> )
##
DeclareAttribute( "RefinedPcGroup", IsPcGroup );

#############################################################################
##
#O  DepthOfPcElement( <pcgs>, <elm> )
##
##  returns the depth of the element <elm> with respect to <pcgs>.
DeclareOperation( "DepthOfPcElement", [ IsModuloPcgs, IsObject ] );

#############################################################################
##
#O  DifferenceOfPcElement( <pcgs>, <left>, <right> )
##
DeclareOperation( "DifferenceOfPcElement", [ IsPcgs, IsObject, IsObject ] );

#############################################################################
##
#O  ExponentOfPcElement( <pcgs>, <elm>, <pos> )
##
##  returns the <pos>-th exponent of <elm> with respect to <pcgs>.
DeclareOperation( "ExponentOfPcElement", 
                  [ IsModuloPcgs, IsObject, IsPosInt ] );

#############################################################################
##
#O  ExponentsOfPcElement( <pcgs>, <elm> )
#O  ExponentsOfPcElement( <pcgs>, <elm>, <posran> )
##
##  returns the exponents of <elm> with respect to <pcgs>. The second form
##  returns the exponents in the positions given in <posran>.
DeclareOperation( "ExponentsOfPcElement",
    [ IsModuloPcgs, IsObject ] );

#############################################################################
##
#O  HeadPcElementByNumber( <pcgs>, <elm>, <num> )
##
DeclareOperation( "HeadPcElementByNumber",
    [ IsModuloPcgs, IsObject, IsInt ] );


#############################################################################
##
#O  LeadingExponentOfPcElement( <pcgs>, <elm> )
##
##  returns the leading exponent of <elm> with respect to <pcgs>.
DeclareOperation( "LeadingExponentOfPcElement",
    [ IsModuloPcgs, IsObject ] );


#############################################################################
##
#O  PcElementByExponents( <pcgs>, <list> )
#O  PcElementByExponentsNC( <pcgs>, <list> )
##
##  returns the element corresponding to the exponent vector <list> with
##  respect to <pcgs>. The exponents in <list> must be in the range of
##  permissible exponents for <pcgs>. *It is not guaranteed that
##  `PcElementByExponents' will reduce the exponents modulo the relative
##  orders*. (You should use the operation `LinearCombinationPcgs' for this
##  purpose.) The NC version does not check that the lengths of the
##  lists fit together and does not check the exponent range.
DeclareGlobalFunction("PcElementByExponents");
DeclareOperation( "PcElementByExponentsNC",
    [ IsModuloPcgs, IsList ] );

#############################################################################
##
#O  LinearCombinationPcgs( <pcgs>, <list> )
##
##  returns the product $\prod_i<pcgs>[i]^{<list>[i]}$.
DeclareGlobalFunction("LinearCombinationPcgs");

#############################################################################
##
#O  ReducedPcElement( <pcgs>, <left>, <right> )
##
DeclareOperation(
    "ReducedPcElement",
    [ IsModuloPcgs, IsObject, IsObject ] );


#############################################################################
##
#O  RelativeOrderOfPcElement( <pcgs>, <elm> )
##
##  The relative order of <elm> with respect to <pcgs>.
DeclareOperation(
    "RelativeOrderOfPcElement",
    [ IsModuloPcgs, IsObject ] );


#############################################################################
##
#O  SumOfPcElement( <pcgs>, <left>, <right> )
##
DeclareOperation(
    "SumOfPcElement",
    [ IsModuloPcgs, IsObject, IsObject ] );


#############################################################################
##

#O  ExtendedIntersectionSumPcgs( <parent-pcgs>, <n>, <u>, <modpcgs> )
##
DeclareOperation(
    "ExtendedIntersectionSumPcgs",
    [ IsModuloPcgs, IsList, IsList, IsObject ] );


#############################################################################
##
#O  IntersectionSumPcgs( <parent-pcgs>, <n>, <u> )
##
DeclareOperation(
    "IntersectionSumPcgs",
    [ IsModuloPcgs, IsList, IsList ] );


#############################################################################
##
#O  NormalIntersectionPcgs( <parent-pcgs>, <n>, <u> )
##
DeclareOperation(
    "NormalIntersectionPcgs",
    [ IsModuloPcgs, IsList, IsList ] );


#############################################################################
##
#O  SumPcgs( <parent-pcgs>, <n>, <u> )
##
DeclareOperation(
    "SumPcgs",
    [ IsModuloPcgs, IsList, IsList ] );


#############################################################################
##
#O  SumFactorizationFunctionPcgs( <parent-pcgs>, <n>, <u>, <modpcgs> )
##
DeclareOperation(
    "SumFactorizationFunctionPcgs",
    [ IsModuloPcgs, IsList, IsList, IsObject ] );


#############################################################################
##

#F  EnumeratorByPcgs( <pcgs>, <poss> )
##
DeclareOperation(
    "EnumeratorByPcgs",
    [ IsModuloPcgs ] );


#############################################################################
##
#O  ExtendedPcgs( <N>, <gens> )
##
DeclareOperation(
    "ExtendedPcgs",
    [ IsModuloPcgs, IsList ] );


#############################################################################
##
#P  IsGenericPcgs( <pcgs> )
##
DeclareProperty( "IsGenericPcgs", IsPcgs );


#############################################################################
##
#F  PcgsByIndependentGeneratorsOfAbelianGroup( <A> )
##
DeclareGlobalFunction( "PcgsByIndependentGeneratorsOfAbelianGroup" );

#############################################################################
##
#F  Pcgs_OrbitStabilizer( <pcgs>,<pnt>,<oprs>,<opr> )
##
##  runs a solvable group orbit-stabilizer algorithm on <pnt> with <pcgs>
##  acting via the images <oprs> and the operation function <opr>. It
##  returns a recors with components `orbit', `stabpcgs' and `lengths', the
##  latter indicating the lengths of the orbit whenever it got extended.
##  This can be used to recompute transversal elements.
##  This function should be used only inside algorithms when speed is
##  essential.
DeclareGlobalFunction( "Pcgs_OrbitStabilizer" );
DeclareGlobalFunction( "Pcs_OrbitStabilizer" );

#############################################################################
##
#E  pcgs.gd . . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

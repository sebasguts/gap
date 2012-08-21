#############################################################################
##
#W  grpperm.tst                 GAP tests                    Alexander Hulpke
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1997
##
##

gap> START_TEST("$Id$");
gap> G1 := TrivialSubgroup (Group ((1,2)));;
gap> G2 := SymmetricGroup ([]);;
gap> G3:=Intersection (G1, G2);;
gap> Size(G3);
1
gap> Pcgs(G3);;

gap> g:=Group((1,2,9)(3,4,5)(6,7,8), (1,4,7)(2,5,8)(3,6,9));;
gap> h:=Group((1,2,9)(3,4,5)(6,7,8));;
gap> (g<h)=(AsSSortedList(g)<AsSSortedList(h));
true

gap> g:=Group( (1,2,3), (2,3)(4,5) );;
gap> IsSolvable(g);
true
gap> RepresentativeOperation(g,(2,5,3), (2,3,4));
(2,3)(4,5)
gap> g:=Group( ( 9,11,10), ( 2, 3, 4),  (14,17,15), (13,16)(15,17), 
>              ( 8,12)(10,11), ( 5, 7)(10,11), (15,16,17), (10,11,12) );;
gap> Sum(ConjugacyClasses(g),Size)=Size(g);
true
gap> g:= Group( (4,8,12),(2,10)(4,8),(1,10)(2,5)(3,12)(4,7)(6,9)(8,11),
>               (1,7)(3,9)(5,11)(6,10) );;
gap> e:=ElementaryAbelianSeriesLargeSteps(DerivedSeries(g));;
gap> List(e,Size);
[ 2592, 324, 162, 81, 1 ]
gap> ForAll([1..Length(e)-1],i->HasElementaryAbelianFactorGroup(e[i],e[i+1]));
true
gap> group:=
> Subgroup( Group( (  1,  2)(  3,  5)(  4,  7)(  6, 10)(  8, 12)(  9, 13)
> ( 14, 19)( 15, 20)( 16, 22)( 17, 23)( 18, 25)( 24, 31)( 26, 33)( 27, 34)
> ( 28, 36)( 29, 38)( 30, 39)( 35, 45)( 37, 46)( 41, 48)( 42, 50)( 43, 51)
> ( 44, 53)( 47, 57)( 49, 59)( 52, 62)( 54, 64)( 55, 65)( 56, 67)( 58, 70)
> ( 60, 73)( 61, 74)( 63, 77)( 66, 80)( 68, 82)( 69, 75)( 71, 84)( 72, 85)
> ( 76, 88)( 78, 90)( 79, 91)( 81, 94)( 83, 97)( 86,100)( 87,101)( 89,102)
> ( 92,104)( 93,105)( 95,103)( 96,106)( 99,107)(108,114)(109,115)(110,112)
> (113,117)(118,119), (  1,  3,  6)(  2,  4,  8)(  5,  9, 14)(  7, 11, 16)
> ( 10, 15, 21)( 12, 17, 24)( 13, 18, 26)( 19, 27, 35)( 20, 28, 37)( 22, 29, 36)
> ( 23, 30, 40)( 25, 32, 42)( 31, 41, 49)( 33, 43, 52)( 34, 44, 54)( 38, 39, 47)
> ( 45, 55, 66)( 46, 56, 68)( 48, 58, 71)( 50, 60, 65)( 51, 61, 75)( 53, 63, 78)
> ( 57, 69, 73)( 59, 72, 86)( 62, 76, 89)( 64, 79, 92)( 67, 81, 95)( 70, 83, 98)
> ( 74, 87, 77)( 80, 93, 88)( 82, 96, 97)( 84, 99,108)( 85, 90,103)( 91,101,110)
> ( 94,100,109)(102,111,104)(105,112,116)(106,113,118)(114,115,117) ), 
> [ (  1,  6)(  2, 25)(  4, 27, 70, 98, 35, 42)(  5, 44)(  7, 11)(  8, 32, 19)
>     (  9, 50, 33,111, 24, 34)( 12,113, 40, 65, 14, 54)( 13, 78)( 15, 21)
>     ( 17,104, 52, 60, 23,106)( 18, 41, 88, 93, 49, 63)( 20,109)( 22,107, 29)
>     ( 26, 53, 31)( 28, 86, 76, 62, 59,100)( 30,118)( 37, 94, 72)
>     ( 38,110, 99,114, 90, 95)( 39, 87, 92, 71, 73,101)( 43,102)
>     ( 45, 85,115, 46, 58, 64)( 47, 67, 84, 91, 57, 74)( 48, 56, 66, 79, 77, 69
>      )( 51, 75)( 55, 68,117,108, 81,103)( 96, 97)(112,116), 
>   (  1,  8, 65, 89, 94, 10, 37, 72, 43, 32,  6, 14, 19, 83, 54)
>     (  2,  9, 78, 86, 67, 63, 52, 76, 93, 55, 44, 49, 42, 24, 82,118,  4, 13,
>       17, 92, 88, 62,104, 18, 85,109, 41, 34, 35, 16)(  3, 21, 15)
>     (  5, 45, 95,117, 59, 29, 47, 74,110, 50, 30, 69, 64, 91, 22, 20,103, 99,
>       46, 60, 26, 87, 39, 90, 27, 25, 66, 81, 73, 53)(  7, 36, 84,106, 38, 51,
>      33, 79, 98, 96, 56,100, 68, 31,116,112, 80, 71, 28,114, 97, 70, 48,111,
>       75, 77, 23,115,107, 11)( 12,102, 40,119,113)( 57,108,105,101, 58, 61) 
>  ] );;
gap> perf:=RepresentativesPerfectSubgroups(group);;
gap> List(perf,Size);
[ 60, 960, 30720, 1 ]

# that's all, folks
gap> STOP_TEST( "grpperm.tst", 2374000000 );

#############################################################################
##
#E  grpperm.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

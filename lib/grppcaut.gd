#############################################################################
##
#W  grppcaut.gd                GAP library                      Bettina Eick
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen, Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
Revision.grppcaut_gd :=
    "@(#)$Id$";

#############################################################################
##
#P IsFrattiniFree
##
DeclareProperty( "IsFrattiniFree", IsGroup );


#############################################################################
##
#I InfoAutGrp
##
DeclareInfoClass( "InfoAutGrp" ); 
DeclareInfoClass( "InfoMatOrb" ); 
DeclareInfoClass( "InfoOverGr" ); 

if not IsBound( CHOP ) then CHOP := false; fi;


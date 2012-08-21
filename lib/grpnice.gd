#############################################################################
##
#W  grpnice.gd                  GAP library                      Frank Celler
##
#H  @(#)$Id$
##
#Y  Copyright (C)  1996,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This  file  contains generic     methods   for groups handled    by  nice
##  monomorphisms..
##
Revision.grpnice_gd :=
    "@(#)$Id$";


#############################################################################
##
#V  NICE_FLAGS
##
NICE_FLAGS := SUM_FLAGS-1;


#############################################################################
##
#A  NiceMonomorphism( <obj> )
##
##  is a homomorphism that is defined (at least) on the whole of <obj> and
##  whose restriction to <obj> is injective. The concrete morphism (and also
##  the image group) will depend on the representation of <obj>.
DeclareAttribute(
    "NiceMonomorphism",
    IsObject );

InstallSubsetMaintenance( NiceMonomorphism,
        IsGroup and HasNiceMonomorphism, IsGroup );


#############################################################################
##
#F  IsNiceMonomorphism( <nhom> )
##
##  This filter indicates that a mappping has been installed as a
##  `NiceMonomorphism'. (Such mappings may need to be handled specially
##  because they should not refer to the `NiceMonomorphism' of the source
##  group again.)
DeclareFilter("IsNiceMonomorphism");

#############################################################################
##
#P  IsCanonicalNiceMonomorphism( <nhom> )
##
##  A `NiceMonomorphism' <nhom> is canonical if the image set will only
##  depend on the set of group elements but not on the generating set. This
##  implies that equal objects will always have equal `NiceObject's.
##  In some situations however this condition would be expensive to
##  acchieve, therefore it is not guaranteed for every nice monomorphism.
DeclareProperty("IsCanonicalNiceMonomorphism",IsGroupGeneralMapping);

#############################################################################
##
#A  NiceObject( <obj> )
##
##  The `NiceObject' of <obj> is the image of <obj> under its
##  `NiceMonomorphism'.
DeclareAttribute(
    "NiceObject",
    IsObject );


#############################################################################
##
#P  IsHandledByNiceMonomorphism( <obj> )
##
##  If this property is `true', high-valued methods that translate all
##  calculations in <obj> in the image under the `NiceMonomorphism' become
##  available for <obj>.
DeclareProperty(
    "IsHandledByNiceMonomorphism",
    IsObject );

InstallSubsetMaintenance( IsHandledByNiceMonomorphism,
    IsHandledByNiceMonomorphism and IsGroup,
    IsGroup);

#############################################################################
##
#O  GroupByNiceMonomorphism( <nice>, <grp> )
##
DeclareOperation(
    "GroupByNiceMonomorphism",
    [ IsGroupHomomorphism, IsGroup ] );


#############################################################################
##

#F  AttributeMethodByNiceMonomorphism( <oper>, <par> )
##
BindGlobal( "AttributeMethodByNiceMonomorphism", function( oper, par )

    # check the argument length
    if 1 <> Length(par)  then
        Error( "need only one argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj )
            return oper( NiceObject(obj) );
        end );
end );


#############################################################################
##
#F  AttributeMethodByNiceMonomorphismCollColl( <oper>, <par> )
##
BindGlobal( "AttributeMethodByNiceMonomorphismCollColl",
    function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;
    par[2] := par[2] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsIdenticalObj,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            if not IsIdenticalObj( NiceMonomorphism(obj1),
                                NiceMonomorphism(obj2) )
            then
                TryNextMethod();
            fi;
            return oper( NiceObject(obj1), NiceObject(obj2) );
        end );
end );


#############################################################################
##
#F  AttributeMethodByNiceMonomorphismCollElm( <oper>, <par> )
##
BindGlobal( "AttributeMethodByNiceMonomorphismCollElm", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsCollsElms,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   img;
            img := ImagesRepresentative( NiceMonomorphism(obj1), obj2 );
            if img = fail  then
                TryNextMethod();
            fi;
            return oper( NiceObject(obj1), img );
        end );
end );

#############################################################################
##
#F  AttributeMethodByNiceMonomorphismElmColl( <oper>, <par> )
##
BindGlobal( "AttributeMethodByNiceMonomorphismElmColl", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[2] := par[2] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsElmsColls,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   img;
            img := ImagesRepresentative( NiceMonomorphism(obj2), obj1 );
            if img = fail  then
                TryNextMethod();
            fi;
            return oper( img,NiceObject(obj2));
        end );
end );


#############################################################################
##

#F  GroupMethodByNiceMonomorphism( <oper>, <par> )
##
BindGlobal( "GroupMethodByNiceMonomorphism", function( oper, par )

    # check the argument length
    if 1 <> Length(par)  then
        Error( "need only one argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj )
            local   nice,  img;
            nice := NiceMonomorphism(obj);
            img  := oper( NiceObject(obj) );
            return GroupByNiceMonomorphism( nice, img );
        end );
end );


#############################################################################
##
#F  GroupMethodByNiceMonomorphismCollOther( <oper>, <par> )
##
BindGlobal( "GroupMethodByNiceMonomorphismCollOther", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj, other )
            local   nice,  img;
            nice := NiceMonomorphism(obj);
            img  := oper( NiceObject(obj), other );
            return GroupByNiceMonomorphism( nice, img );
        end );
end );


#############################################################################
##
#F  GroupMethodByNiceMonomorphismCollColl( <oper>, <par> )
##
BindGlobal( "GroupMethodByNiceMonomorphismCollColl", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;
    par[2] := par[2] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsIdenticalObj,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  img;
            nice := NiceMonomorphism(obj1);
            if not IsIdenticalObj( nice, NiceMonomorphism(obj2) )  then
                TryNextMethod();
            fi;
            img := oper( NiceObject(obj1), NiceObject(obj2) );
            return GroupByNiceMonomorphism( nice, img );
        end );
end );


#############################################################################
##
#F  GroupMethodByNiceMonomorphismCollElm( <oper>, <par> )
##
BindGlobal( "GroupMethodByNiceMonomorphismCollElm", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsCollsElms,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  img,  img1;
            nice := NiceMonomorphism(obj1);
            img  := ImagesRepresentative( nice, obj2 );
            if img = fail  then
                TryNextMethod();
            fi;
            img1 := oper( NiceObject(obj1), img );
            return GroupByNiceMonomorphism( nice, img1 );
        end );
end );


#############################################################################
##
#F  SubgroupMethodByNiceMonomorphism( <oper>, <par> )
##
BindGlobal( "SubgroupMethodByNiceMonomorphism", function( oper, par )

    # check the argument length
    if 1 <> Length(par)  then
        Error( "need only one argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj )
            local   nice,  img,  sub;
            nice := NiceMonomorphism(obj);
            img  := oper( NiceObject(obj) );
            sub  := GroupByNiceMonomorphism( nice, img );
            SetParent( sub, obj );
            return sub;
        end );
end );

#############################################################################
##
#F  SubgroupsMethodByNiceMonomorphism( <oper>, <par> )
##
BindGlobal( "SubgroupsMethodByNiceMonomorphism", function( oper, par )

    # check the argument length
    if 1 <> Length(par)  then
        Error( "need only one argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj )
            local   nice,  img,  sub,i;
            nice := NiceMonomorphism(obj);
            img  := ShallowCopy(oper( NiceObject(obj) ));
	    for i in [1..Length(img)] do
	      sub  := GroupByNiceMonomorphism( nice, img[i] );
	      SetParent( sub, obj );
	      img[i]:=sub;
	    od;
            return img;
        end );
end );


#############################################################################
##
#F  SubgroupMethodByNiceMonomorphismCollOther( <oper>, <par> )
##
BindGlobal( "SubgroupMethodByNiceMonomorphismCollOther",
    function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj, other )
            local   nice,  img,  sub;
            nice := NiceMonomorphism(obj);
            img  := oper( NiceObject(obj), other );
            sub  := GroupByNiceMonomorphism( nice, img );
            SetParent( sub, obj );
            return sub;
        end );
end );


#############################################################################
##
#F  SubgroupMethodByNiceMonomorphismCollColl( <oper>, <par> )
##
BindGlobal( "SubgroupMethodByNiceMonomorphismCollColl", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;
    par[2] := par[2] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsIdenticalObj,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  img,  sub;
            if not IsSubgroup( obj1, obj2 )  then
                TryNextMethod();
            fi;
            nice := NiceMonomorphism(obj1);
            img := oper( NiceObject(obj1), Image(nice,obj2) );
            sub := GroupByNiceMonomorphism( nice, img );
            SetParent( sub, obj1 );
            return sub;
        end );
end );


#############################################################################
##
#F  SubgroupMethodByNiceMonomorphismCollElm( <oper>, <par> )
##
BindGlobal( "SubgroupMethodByNiceMonomorphismCollElm", function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsCollsElms,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  img,  img1,  sub;
            nice := NiceMonomorphism(obj1);
            img  := ImagesRepresentative( nice, obj2 );
            if img = fail  then
                TryNextMethod();
            fi;
            img1 := oper( NiceObject(obj1), img );
            sub  := GroupByNiceMonomorphism( nice, img1 );
            SetParent( sub, obj1 );
            return sub;
        end );
end );


#############################################################################
##

#F  PropertyMethodByNiceMonomorphism( <oper>, <par> )
##
DeclareSynonym( "PropertyMethodByNiceMonomorphism",
    AttributeMethodByNiceMonomorphism );


#############################################################################
##
#F  PropertyMethodByNiceMonomorphismCollColl( <oper>, <par> )
##
DeclareSynonym( "PropertyMethodByNiceMonomorphismCollColl",
    AttributeMethodByNiceMonomorphismCollColl );


#############################################################################
##
#F  PropertyMethodByNiceMonomorphismCollElm( <oper>, <par> )
##
DeclareSynonym( "PropertyMethodByNiceMonomorphismCollElm",
    AttributeMethodByNiceMonomorphismCollElm );


#############################################################################
##
#F  PropertyMethodByNiceMonomorphismElmColl( <oper>, <par> )
##
DeclareSynonym( "PropertyMethodByNiceMonomorphismElmColl",
    AttributeMethodByNiceMonomorphismElmColl );


#############################################################################
##

#F  GroupSeriesMethodByNiceMonomorphism( <oper>, <par> )
##
BindGlobal( "GroupSeriesMethodByNiceMonomorphism", function( oper, par )

    # check the argument length
    if 1 <> Length(par)  then
        Error( "need only one argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj )
            local   nice,  list,  i;
            nice := NiceMonomorphism(obj);
            list := ShallowCopy( oper( NiceObject(obj) ) );
            for i  in [ 1 .. Length(list) ]  do
                list[i] := GroupByNiceMonomorphism( nice, list[i] );
                SetParent( list[i], obj );
            od;
            return list;
        end );
end );


#############################################################################
##
#F  GroupSeriesMethodByNiceMonomorphismCollOther( <oper>, <par> )
##
BindGlobal( "GroupSeriesMethodByNiceMonomorphismCollOther",
    function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two argument for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        true,
        par,
        NICE_FLAGS,
        function( obj, other )
            local   nice,  list,  i;
            nice := NiceMonomorphism(obj);
            list := ShallowCopy( oper( NiceObject(obj), other ) );
            for i  in [ 1 .. Length(list) ]  do
                list[i] := GroupByNiceMonomorphism( nice, list[i] );
                SetParent( list[i], obj );
            od;
            return list;
        end );
end );


#############################################################################
##
#F  GroupSeriesMethodByNiceMonomorphismCollColl( <oper>, <par> )
##
BindGlobal( "GroupSeriesMethodByNiceMonomorphismCollColl",
    function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;
    par[2] := par[2] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsIdenticalObj,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  list,  i;
            nice := NiceMonomorphism(obj1);
            if not IsIdenticalObj( nice, NiceMonomorphism(obj2) )  then
                TryNextMethod();
            fi;
            list := ShallowCopy(oper(NiceObject(obj1),NiceObject(obj2)));
            for i  in [ 1 .. Length(list) ]  do
                list[i] := GroupByNiceMonomorphism( nice, list[i] );
                SetParent( list[i], obj1 );
            od;
            return list;
        end );
end );


#############################################################################
##
#F  GroupSeriesMethodByNiceMonomorphismCollElm( <oper>, <par> )
##
BindGlobal( "GroupSeriesMethodByNiceMonomorphismCollElm",
    function( oper, par )

    # check the argument length
    if 2 <> Length(par)  then
        Error( "need two arguments for ", NameFunction(oper) );
    fi;
    par    := ShallowCopy(par);
    par[1] := par[1] and IsHandledByNiceMonomorphism;

    # install the method
    InstallOtherMethod( oper,
        "handled by nice monomorphism",
        IsCollsElms,
        par,
        NICE_FLAGS,
        function( obj1, obj2 )
            local   nice,  img,  list,  i;
            nice := NiceMonomorphism(obj1);
            img  := ImagesRepresentative( nice, obj2 );
            if img = fail  then
                TryNextMethod();
            fi;
            list := ShallowCopy( oper( NiceObject(obj1), img ) );
            for i  in [ 1 .. Length(list) ]  do
                list[i] := GroupByNiceMonomorphism( nice, list[i] );
                SetParent( list[i], obj1 );
            od;
            return list;
        end );
end );


#############################################################################
##

#E  grpnice.gd  . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
##

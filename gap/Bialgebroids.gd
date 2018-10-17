#
# Bialgebroids: Bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Bialgebroids as preadditive categories generated by enhanced quivers

# our info class:
DeclareInfoClass( "InfoBialgebroids" );
SetInfoLevel( InfoBialgebroids, 1 );

####################################
#
#! @Section Categories
#
####################################

#! @Description
#!  The &GAP; category of objects in an algebroid.
DeclareCategory( "IsCapCategoryObjectInAlgebroid",
        IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in an algebroid.
DeclareCategory( "IsCapCategoryMorphismInAlgebroid",
        IsCapCategoryMorphism );

#! @Description
#!  The &GAP; category of algebroids.
DeclareCategory( "IsAlgebroid",
        IsCapCategory );

#! @Description
#!  The &GAP; category of morphisms of algebroids.
DeclareCategory( "IsAlgebroidMorphism",
        IsCapFunctor );

#! @Description
#!  The &GAP; category of algebroids.
DeclareCategory( "IsAlgebraAsCategory",
        IsAlgebroid );

####################################
#
#! @Section Properties
#
####################################

#! @Description
#!  Is the category <A>A</A> finitely presented.
#!  This property is true by construction for algebroids generated by finite quivers.
#! @Arguments A
DeclareProperty( "IsFinitelyPresentedCategory",
        IsCapCategory );

Add( CAP_INTERNAL_CAN_COMPUTE_FILTER_LIST!.MathematicalPropertiesOfCategories,
     "IsFinitelyPresentedCategory" );

#! @Description
#!  Check whether the algebroid <A>A</A> is commutative.
#! @Arguments A
#! @Returns true or false
DeclareProperty( "IsCommutative",
        IsAlgebroid );

#! @Description
#!  Check whether <A>B</A> is counitary.
#! @Arguments B
#! @Returns true or false
DeclareProperty( "IsCounitary",
        IsAlgebroid );

#! @Description
#!  Check whether <A>B</A> is coassociative.
#! @Arguments B
#! @Returns true or false
DeclareProperty( "IsCoassociative",
        IsAlgebroid );

#! @Description
#!  Check whether the antipode of <A>B</A> is actually an antipode.
#! @Arguments B
#! @Returns true or false
DeclareProperty( "IsHopfAlgebroid",
        IsAlgebroid );
####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The quiver underlying the algebroid <A>A</A>.
#! @Arguments A
#! @Returns a &QPA; quiver
DeclareAttribute( "UnderlyingQuiver",
        IsAlgebroid );

#! @Description
#!  The quiver algebra (=path algebra with relations) underlying the algebroid <A>A</A>.
#! @Arguments A
#! @Returns a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebra",
        IsAlgebroid );

#! @Description
#!  The base ring of the algebroid <A>A</A>.
#! @Arguments A
#! @Returns a ring
DeclareAttribute( "BaseRing",
        IsAlgebroid );

#! @Description
#!  The finite set of objects of the finitely presented algebroid <A>A</A>.
#! @Arguments A
#! @Returns a list
DeclareAttribute( "SetOfObjects",
        IsAlgebroid );

#! @Description
#!  The finite set of morphisms generating the finitely presented algebroid <A>A</A>.
#! @Arguments A
#! @Returns a list
DeclareAttribute( "SetOfGeneratingMorphisms",
        IsAlgebroid );

#! @Description
#!  The relations of the algebroid <A>A</A> corresponding to
#!  <C>RelationsOfAlgebra( UnderlyingQuiverAlgebra( <A>A</A> ) )</C>.
#! @Arguments A
#! @Returns a &QPA; path algebra
DeclareAttribute( "RelationsOfAlgebroid",
        IsAlgebroid );

#! @Description
#!  The counit of the bialgebroid <A>B</A>.
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "Counit",
        IsAlgebroid );

#! @Description
#!  The comultiplication of the bialgebroid <A>B</A>.
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "Comultiplication",
        IsAlgebroid );

DeclareAttribute( "Multiplication",
        IsAlgebraAsCategory );

DeclareAttribute( "Unit",
        IsAlgebraAsCategory );

#! @Description
#!  The antipode of the Hopf algebroid <A>B</A>.
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "Antipode",
        IsAlgebroid );

#! @Description
#!  The vertex of the quiver underlying the object <A>obj</A> in an algebroid.
#! @Arguments obj
#! @Returns a vertex in a &QPA; quiver
DeclareAttribute( "UnderlyingVertex",
        IsCapCategoryObjectInAlgebroid );

#! @Description
#!  The quiver algebra element underlying the morphism <A>mor</A> in an algebroid.
#! @Arguments mor
#! @Returns an element in a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebraElement",
        IsCapCategoryMorphismInAlgebroid );

#! @Description
#!  The <A>n</A>-th power of the algebroid <A>A</A>.
#!  Admissible values for <A>n</A> are $0,1,2$.
#! @Arguments A, n
#! @Returns a &CAP; category
DeclareOperation( "POW",
        [ IsAlgebroid, IsInt ] );

DeclareOperation( "\*",
        [ IsAlgebroid, IsAlgebroid ] );

DeclareOperation("TensorProductOnObjects",
        [ IsAlgebroid, IsAlgebroid ] );

#! @Description
#!  Given an object <A>a</A> in an algebroid A and an object <A>b</A> in an algebroid B and the tensor product <A>T</A> of A and B, return the tensor product of a and b in T.
#! @Arguments a, b, T
#! @Returns a morphism in a &CAP; category
DeclareOperation("ElementaryTensor",
        [ IsCapCategoryObjectInAlgebroid, IsCapCategoryObjectInAlgebroid, IsAlgebroid ] );

#! @Description
#!  Given an object <A>a</A> in an algebroid A and a morphism <A>g</A> in an algebroid B and the tensor product <A>T</A> of A and B, return the tensor product of a and g in T.
#! @Arguments a, g, T
#! @Returns a morphism in a &CAP; category
DeclareOperation("ElementaryTensor",
        [ IsCapCategoryObjectInAlgebroid, IsCapCategoryMorphismInAlgebroid, IsAlgebroid ] );

#! @Description
#!  Given a morphism <A>f</A> in an algebroid A and an object <A>b</A> in an algebroid B and the tensor product <A>T</A> of A and B, return the tensor product of f and b in T.
#! @Arguments f, b, T
#! @Returns a morphism in a &CAP; category
DeclareOperation("ElementaryTensor",
        [ IsCapCategoryMorphismInAlgebroid, IsCapCategoryObjectInAlgebroid, IsAlgebroid ] );

DeclareAttribute( "BijectionBetweenPairsAndElementaryTensors",
        IsQuiverAlgebra );

DeclareAttribute( "DecompositionOfMorphismInAlgebroid",
        IsCapCategoryMorphismInAlgebroid );

DeclareAttribute( "DecompositionOfMorphismInSquareOfAlgebroid",
        IsCapCategoryMorphismInAlgebroid );

####################################
#
#! @Section Operations
#
####################################

DeclareOperation( "DecomposeQuiverAlgebraElement",
        [ IsQuiverAlgebraElement ] );

#! @Description
#!  Apply the functor defined by the records <A>images_of_objects</A> and <A>images_of_morphisms</A> to the quiver algebra element <A>p</A>.
#! @Arguments images_of_objects, images_of_morphisms, path, contravariant
#! @Returns a morphism in a &CAP; category
DeclareOperation( "ApplyToQuiverAlgebraElement",
        [ IsRecord, IsRecord, IsQuiverAlgebraElement, IsBool ] );

####################################
#
#! @Section Constructors
#
####################################

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_ALGEBROID" );

#! @Description
#!  Construct the algebroid associated to the path $R$-algebra <A>Rq</A>
#!  of the quiver $q$ modulo the relations <A>L</A> as an $R$-linear category.
#! @Arguments Rq
#! @Returns a &CAP; category
#! @Group Algebroid
DeclareAttribute( "Algebroid",
        IsQuiverAlgebra );

#! @Arguments Rq, L
#! @Group Algebroid
DeclareOperation( "Algebroid",
        [ IsPathAlgebra, IsList ] );

#! @Arguments R, q
#! @Group Algebroid
DeclareOperation( "Algebroid",
        [ IsHomalgRing, IsQuiver ] );

#! @Description
#!  Construct, using the record of images <A>ImagesOfObject</A> and <A>ImagesOfMorphisms</A>,
#!  a functor with source the finitely presented algebroid <A>A</A>.
#!  The record <A>ImagesOfObject</A> is supposed to contain the images of the objects of <A>A</A>.
#!  The record <A>ImagesOfMorphisms</A> is supposed to contain the images of the set of generating morphisms of <A>A</A>.
#! @Arguments A, ImagesOfObject, ImagesOfMorphisms
#! @Returns a &CAP; functor
DeclareOperation( "CapFunctor",
        [ IsAlgebroid, IsRecord, IsRecord ] );

#! @Description
#!  Construct, using the record of images <A>eta</A>, a natural transformation
#!  from the functor <A>F</A> to the parallel functor <A>G</A>.
#! @Arguments eta, F, G
#! @Returns a &CAP; natural transformation
DeclareOperation( "NaturalTransformation",
        [ IsRecord, IsCapFunctor, IsCapFunctor ] );

#! @Description
#!  Add to the algebroid <A>A</A> a counit and a comultiplication
#!  using the defining records <A>counit</A> and <A>comult</A>, respectively.
#! @Arguments A, counit, comult
#! @Returns a &CAP; category
DeclareOperation( "AddBialgebroidStructure",
        [ IsAlgebroid, IsRecord, IsRecord ] );

#! @Description
#!  Add to the bialgebroid <A>B</A> an antipode <A>S</A>.
#! @Arguments B, S
#! @Returns a &CAP; category
DeclareOperation( "AddAntipode",
        [ IsAlgebroid, IsRecord ] );

#! @Description
#!  The constructor of objects in an algebroid <A>A</A> given a vertex <A>V</A>
#!  in the underlying quiver.
#! @Arguments A, V
#! @Returns an object in a &CAP; category
#! @Group ObjectInAlgebroid
DeclareOperation( "ObjectInAlgebroid",
        [ IsAlgebroid, IsVertex ] );

#! @Description
#!  The constructor of morphisms in an algebroid given the source <A>S</A>,
#!  the target <A>T</A>, and the underlying quiver algebra element <A>path</A>.
#!  If neither <A>S</A> nor <A>T</A> are provided they are read off from <A>path</A>.
#! @Arguments S, path, T
#! @Returns a morphism in a &CAP; category
#! @Group MorphismInAlgebroid
DeclareOperation( "MorphismInAlgebroid",
        [ IsCapCategoryObjectInAlgebroid, IsQuiverAlgebraElement, IsCapCategoryObjectInAlgebroid ] );

#! @Arguments path
#! @Group MorphismInAlgebroid
DeclareOperation( "MorphismInAlgebroid",
        [ IsQuiverAlgebraElement ] );

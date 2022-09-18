# SPDX-License-Identifier: GPL-2.0-or-later
# Algebroids: Algebroids and bialgebroids as preadditive categories generated by enhanced quivers
#
# Declarations
#

#! @Chapter Finitely presented categories generated by enhanced quivers

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#!  The &GAP; category of finitely presented categories.
DeclareCategory( "IsFpCategory",
        IsCapCategory );

#! @Description
#!  The &GAP; category of algebras.
DeclareCategory( "IsMonoidAsCategory",
        IsFpCategory );

#! @Description
#!  The &GAP; category of cells in a finitely presented category.
DeclareCategory( "IsCellInFpCategory",
        IsCapCategoryCell );

#! @Description
#!  The &GAP; category of objects in a finitely presented category.
DeclareCategory( "IsObjectInFpCategory",
        IsCellInFpCategory and IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a finitely presented category.
DeclareCategory( "IsMorphismInFpCategory",
        IsCellInFpCategory and IsCapCategoryMorphism );

####################################
#
#! @Section Properties
#
####################################

#! @Description
#!  Is the category <A>C</A> finitely presented.
#!  This property is true by construction for finitely presented categories generated by finite quivers.
#! @Arguments C
AddCategoricalProperty(
        [ "IsFinitelyPresentedCategory", "IsFinitelyPresentedCategory" ] );

#! @Description
#!  Check whether the finitely presented category <A>C</A> is commutative.
#! @Arguments C
#! @Returns true or false
DeclareProperty( "IsCommutative",
        IsFpCategory );

#! @Description
#!  Check whether <A>B</A> is counitary.
#! @Arguments B
#! @Returns true or false
DeclareProperty( "IsCounitary",
        IsFpCategory );

#! @Description
#!  Check whether <A>B</A> is coassociative.
#! @Arguments B
#! @Returns true or false
DeclareProperty( "IsCoassociative",
        IsFpCategory );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The quiver underlying the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a &QPA; quiver
DeclareAttribute( "UnderlyingQuiver",
        IsFpCategory );

#! @Description
#!  The quiver algebra (=path algebra with relations) underlying the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebra",
        IsFpCategory );


#! @Description
#!  The number of morphisms in the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a nonnegative integer
DeclareAttribute( "Size",
        IsFpCategory );

#! @Description
#!  The finite set of objects of the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfObjects",
        IsFpCategory );
CapJitAddTypeSignature( "SetOfObjects", [ IsCapCategory ],
  function ( input_types )
    
    Assert( 0, IsFpCategory( input_types[1].category ) );
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfObjectOfCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Assigns the objects of the finitely presented category <A>C</A> to global variables.
#!  Names of the variables are the concatenation of <A>label</A> with the names of the defining vertices.
#! @Arguments C, label
#! @Returns nothing
DeclareOperation( "AssignSetOfObjects",
        [ IsFpCategory, IsString ] );

#! @Description
#!  The finite set of morphisms generating the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a list
DeclareAttribute( "SetOfGeneratingMorphisms",
        IsFpCategory );
CapJitAddTypeSignature( "SetOfGeneratingMorphisms", [ IsCapCategory ],
  function ( input_types )
    
    Assert( 0, IsFpCategory( input_types[1].category ) );
    
    return rec( filter := IsList,
                element_type := CapJitDataTypeOfMorphismOfCategory( input_types[1].category ) );
    
end );

#! @Description
#!  The subset of the generating morphisms that start at <A>obj_1</A> and ends at <A>obj_2</A>.
#! @Arguments C, obj_1, obj_2
#! @Returns a list
DeclareOperation( "SetOfGeneratingMorphisms",
        [ IsFpCategory, IsObjectInFpCategory, IsObjectInFpCategory ] );

#! @Description
#!  The subset of the generating morphisms that start at <A>obj_1</A> and ends at <A>obj_2</A>.
#! @Arguments obj_1, obj_2
#! @Returns a list
DeclareOperation( "SetOfGeneratingMorphisms",
        [ IsObjectInFpCategory, IsObjectInFpCategory ] );

#! @Description
#!  Delegates to <C>SetOfGeneratingMorphisms</C>( <A>C</A>, <C>SetOfObjects</C>(<A>C</A>)[<A>i</A>], <C>SetOfObjects</C>(<A>C</A>)[<A>j</A>] ).
#! @Arguments C, i, j
#! @Returns a list
DeclareOperation( "SetOfGeneratingMorphisms",
        [ IsFpCategory, IsInt, IsInt ] );

#! @Description
#!  Assigns the generating morphisms of the finitely presented category <A>C</A> to global variables.
#!  Names of the variables are the concatenation of <A>label</A> with the names of the defining arrows.
#! @Arguments C, label
#! @Returns nothing
DeclareOperation( "AssignSetOfGeneratingMorphisms",
        [ IsFpCategory, IsString ] );

#! @Description
#!  The relations of the finitely presented category <A>C</A> corresponding to
#!  <C>RelationsOfAlgebra( UnderlyingQuiverAlgebra( <A>C</A> ) )</C>.
#! @Arguments C
#! @Returns a &QPA; path algebra
DeclareAttribute( "RelationsOfFpCategory",
        IsFpCategory );

#! @Description
#!  The finitely presented category defined by the opposite of the underlying quiver with relations.
#! @Arguments C
#! @Returns a &CAP; category
DeclareAttribute( "OppositeFpCategory",
        IsFpCategory );

DeclareAttribute( "Multiplication",
        IsMonoidAsCategory );

DeclareAttribute( "Unit",
        IsMonoidAsCategory );

#! @Description
#!  The antipode of the Hopf finitely presented category <A>B</A>.
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "Antipode",
        IsFpCategory );

#! @Description
#!  The vertex of the quiver underlying the object <A>obj</A> in a finitely presented category.
#! @Arguments obj
#! @Returns a vertex in a &QPA; quiver
DeclareAttribute( "UnderlyingVertex",
        IsObjectInFpCategory );

#! @Description
#!  The quiver algebra element underlying the morphism <A>mor</A> in a finitely presented category.
#! @Arguments mor
#! @Returns an element in a &QPA; path algebra
DeclareAttribute( "UnderlyingQuiverAlgebraElement",
        IsMorphismInFpCategory );

##
DeclareAttribute( "BasisPathOfPathAlgebraBasisElement",
       IsQuiverAlgebraElement );

CapJitAddTypeSignature( "BasisPathOfPathAlgebraBasisElement", [ IsQuiverAlgebraElement ], IsPath );

#! @Description
#!  The underlying algebra of the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a ring
DeclareAttribute( "UnderlyingAlgebra",
        IsFpCategory );

#! @Description
#!  The parity of the finitely presented category <A>C</A>.
#! @Arguments C
#! @Returns a string ("left" or "right")
DeclareAttribute( "Parity",
        IsFpCategory );

#! @Description
#!  The <A>n</A>-th power of the finitely presented category <A>C</A>.
#!  Admissible values for <A>n</A> are $0,1,2$.
#! @Arguments C, n
#! @Returns a &CAP; category
DeclareOperation( "POW",
        [ IsFpCategory, IsInt ] );

#! @Description
#!  The input is a finitely presented category <A>C</A> equipped with a homomorphism structure
#!  with values in the skeletal category <C>SkeletalFinSets</C> of finite sets.
#!  The output is the nerve of <A>B</A> truncated in degree $2$,
#!  as a presheaf on <C>SimplicialCategoryTruncatedInDegree</C>($2$)
#!  with values in <C>SkeletalFinSets</C>.
#! @Arguments C
#! @Returns a &CAP; functor
DeclareAttribute( "NerveTruncatedInDegree2AsFunctor",
        IsFpCategory );
#! @InsertChunk NerveTruncatedInDegree2AsFunctor

DeclareAttribute( "YonedaNaturalEpimorphisms", IsCapCategory );

#! @Description
#!  The input is a finitely presented category <A>B</A>. The output is a natural morphism.
#!  Its source is the functor $B \to H, c \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,c),
#!  \psi \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,\psi)$.
#!  Its targe is the constant functor of $0$-cells
#!  $B \to H, c \mapsto B_0, \psi \mapsto \mathrm{id}_{B_0}$.
#! @Arguments B
#! @Returns a &CAP; natural transformation
DeclareAttribute( "YonedaFibrationAsNaturalTransformation", IsCapCategory );

#! @Description
#!  The input is a finitely presented category <A>B</A>. The output is a natural epimorphism.
#!  Its source is the functor
#!  $B \to H, c \mapsto \sqcup_{a,b\in B} \mathrm{Hom}(a,b) \times \mathrm{Hom}(b,c),
#!  \psi \mapsto \sqcup_{a,b\in B} \mathrm{Hom}(1_a,1_b) \times \mathrm{Hom}(b,\psi)$.
#!  Its target is the functor $B \to H, c \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,c),
#!  \psi \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,\psi)$.
#! @Arguments B
#! @Returns a &CAP; natural transformation
DeclareAttribute( "YonedaProjectionAsNaturalEpimorphism", IsCapCategory );

#! @Description
#!  The input is a finitely presented category <A>B</A>. The output is a natural epimorphism.
#!  Its source is the functor
#!  $B \to H, c \mapsto \sqcup_{a,b\in B} \mathrm{Hom}(a,b) \times \mathrm{Hom}(b,c),
#!  \psi \mapsto \sqcup_{a,b\in B} \mathrm{Hom}(1_a,1_b) \times \mathrm{Hom}(b,\psi)$.
#!  Its target is the functor $B \to H, c \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,c),
#!  \psi \mapsto \sqcup_{a\in B} \mathrm{Hom}(a,\psi)$.
#! @Arguments B
#! @Returns a &CAP; natural transformation
DeclareAttribute( "YonedaCompositionAsNaturalEpimorphism", IsCapCategory );
#! @InsertChunk YonedaCompositionAsNaturalEpimorphism

DeclareAttribute( "TruthMorphismOfTrueToSieveFunctorAndEmbedding", IsFpCategory );
DeclareAttribute( "EmbeddingOfSieveFunctor", IsFpCategory );

#! @Description
#!  Return the truth morphism of true from terminal functor
#!  to the functor of sieves from <C>OppositeFpCategory</C>( <A>B</A> )
#!  to <C>RangeCategoryOfHomomorphismStructure</C>( <A>B</A> ).
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "TruthMorphismOfTrueToSieveFunctor", IsFpCategory );
#! @InsertChunk SieveFunctor

#! @Description
#!  Return the functor of sieves from <C>OppositeFpCategory</C>( <A>B</A> )
#!  to <C>RangeCategoryOfHomomorphismStructure</C>( <A>B</A> ).
#! @Arguments B
#! @Returns a &CAP; functor
DeclareAttribute( "SieveFunctor", IsFpCategory );
#! @InsertChunk SieveFunctor

####################################
#
#! @Section Operations
#
####################################

#! @Description
#!  Return the cell <A>c</A> in a finitely presented category <M>C</M> = <C>CapCategory</C>(<A>c</A>)
#!  interpreted as a cell in <C>OppositeFpCategory</C>(<M>C</M>).
#! @Arguments C, c
#! @Returns a cell in a finitely presented category
DeclareOperation( "Opposite",
        [ IsFpCategory, IsCellInFpCategory ] );

#! @Arguments str
DeclareOperation( "TrivialCategory",
        [ IsString ] );

#! @Arguments C, D
DeclareOperation( "\*",
        [ IsFpCategory, IsFpCategory ] );

#! @Description
#!  Given an object <A>a</A> in a finitely presented category A and an object <A>b</A> in a finitely presented category B and the tensor product <A>T</A> of A and B, return the tensor product of a and b in T.
#! @Arguments a, b, T
#! @Returns a morphism in a &CAP; category
DeclareOperation( "ElementaryTensor",
        [ IsObjectInFpCategory, IsObjectInFpCategory, IsFpCategory ] );

#! @Description
#!  Given an object <A>a</A> in a finitely presented category A and a morphism <A>g</A> in a finitely presented category B and the tensor product <A>T</A> of A and B, return the tensor product of a and g in T.
#! @Arguments a, g, T
#! @Returns a morphism in a &CAP; category
DeclareOperation( "ElementaryTensor",
        [ IsObjectInFpCategory, IsMorphismInFpCategory, IsFpCategory ] );

#! @Description
#!  Given a morphism <A>f</A> in a finitely presented category A and an object <A>b</A> in a finitely presented category B and the tensor product <A>T</A> of A and B, return the tensor product of f and b in T.
#! @Arguments f, b, T
#! @Returns a morphism in a &CAP; category
DeclareOperation( "ElementaryTensor",
        [ IsMorphismInFpCategory, IsObjectInFpCategory, IsFpCategory ] );

####################################
#
#! @Section Constructors
#
####################################

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_FP_CATEGORY" );

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_HOM_STRUCTURE_OF_FP_CATEGORY" );

DeclareGlobalFunction( "ADD_FUNCTIONS_FOR_RANDOM_METHODS_OF_FP_CATEGORY" );

DeclareOperation( "Category",
        [ IsQuiverAlgebra, IsCapCategory ] );

# do not turn this into an attribute:
DeclareOperation( "Category",
        [ IsQuiverAlgebra ] );

DeclareOperation( "Category",
        [ IsPathAlgebra, IsList ] );

#! @Description
#!  Construct the finitely presented category generated by the quiver <A>q</A>,
#!  possibly modulo the relations <A>L</A>.
#! @Arguments q
#! @Returns a &CAP; category
#! @Group FpCategory
DeclareOperation( "FreeCategory",
        [ IsQuiver ] );

#! @Arguments q, L
#! @Group FpCategory
DeclareOperation( "Category",
        [ IsQuiver, IsList ] );

#! @Arguments C, L
#! @Group FpCategory
DeclareOperation( "/",
        [ IsFpCategory, IsList ] );

#! @Description
#!  Construct a functor with source the finitely presented category <A>C</A> and target <A>B</A> using
#!  the two defining lists of images <A>images_of_objects</A> and <A>images_of_generating_morphisms</A>.
#!  The order of their entries must correspond to that of the vertices and arrows of the underlying quiver.
#! @Arguments A, images_of_objects, images_of_generating_morphisms, B, covariant
#! @Group CapFunctor
DeclareOperation( "CapFunctor",
        [ IsFpCategory, IsList, IsList, IsCapCategory, IsBool ] );

#! @Arguments A, images_of_objects, images_of_generating_morphisms, B
#!  If the last boolean argument <A>covariant</A> is not specified it defaults to <C>true</C>.
#! @Group CapFunctor
DeclareOperation( "CapFunctor",
        [ IsFpCategory, IsList, IsList, IsCapCategory ] );

#! @Description
#!  Alternatively one could specify the records of images <A>rec_images_of_objects</A> and <A>rec_images_of_generating_morphisms</A>.
#!  The record <A>rec_images_of_objects</A> is supposed to contain the images of the objects of <A>C</A>.
#!  The record <A>rec_images_of_generating_morphisms</A> is supposed to contain the images of the set of generating morphisms of <A>C</A>.
#! @Arguments A, rec_images_of_objects, rec_images_of_generating_morphisms, covariant
#! @Returns a &CAP; functor
#! @Group CapFunctor
DeclareOperation( "CapFunctor",
        [ IsFpCategory, IsRecord, IsRecord, IsBool ] );

#! @Arguments A, rec_images_of_objects, rec_images_of_generating_morphisms
#! @Group CapFunctor
DeclareOperation( "CapFunctor",
        [ IsFpCategory, IsRecord, IsRecord ] );

#! @Description
#!  In the case of two arguments, where the second argument is an object <A>obj</A>
#!  then the output is the constant functor having <A>obj</A> as the value on objects
#!  and <C>IdentityMorphism</C>(<A>obj</A>) as the value on morphisms.
#! @Arguments A, obj
#! @Group CapFunctor
DeclareOperation( "CapFunctor",
        [ IsFpCategory, IsCapCategoryObject ] );

#! @Description
#!  The constructor of objects in a finitely presented category <A>C</A> given a vertex <A>V</A>
#!  in the underlying quiver.
#! @Arguments A, V
#! @Returns an object in a &CAP; category
#! @Group ObjectInFpCategory
DeclareOperation( "ObjectInFpCategory",
        [ IsFpCategory, IsQuiverVertex ] );

#! @Description
#!  Delegates to <C>ObjectInFpCategory</C>( <A>C</A>,  <A>V</A> ).
#! @Arguments V, A
#! @Returns an object in a &CAP; category
if false then
DeclareOperation( "\/", [ IsQuiverVertex, IsFpCategory ] );
fi;

DeclareOperation( "MorphismInFpCategory",
        [ IsObjectInFpCategory, IsQuiverAlgebraElement, IsObjectInFpCategory ] );

DeclareOperation( "MorphismInFpCategory",
        [ IsFpCategory, IsQuiverAlgebraElement ] );

#! @Description
#!  The constructor of morphisms in a finitely presented category <A>C</A> given the source <A>S</A>,
#!  the target <A>T</A>, and the underlying path <A>path</A>.
#!  If neither <A>S</A> nor <A>T</A> are provided they are read off from <A>path</A>.
#! @Arguments S, path, T
#! @Returns a morphism in a &CAP; category
#! @Group MorphismInFpCategory
DeclareOperation( "MorphismInFpCategory",
        [ IsObjectInFpCategory, IsPath, IsObjectInFpCategory ] );

#! @Arguments A, path
#! @Group MorphismInFpCategory
DeclareOperation( "MorphismInFpCategory",
        [ IsFpCategory, IsPath ] );

#! @Description
#!  Delegates to <C>MorphismInFpCategory</C>( <A>path</A> ).
#! @Arguments path, A
#! @Returns a morphism in a &CAP; category
DeclareOperation( "\/", [ IsPath, IsFpCategory ] );

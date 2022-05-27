#! @Chunk SnakeInFreeAbelian

LoadPackage( "FunctorCategories" );

#! @Example
q := RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" );
#! q(4)[a:1->2,b:2->3,c:3->4]
Fq := FreeCategory( q );
#! FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) )
QQ := HomalgFieldOfRationals( );
#! Q
Qq := QQ[Fq];
#! Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
A := Qq / [ Qq.abc ];
#! Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#! / relations
LoadPackage( "FreydCategoriesForCAP" );
#! true
PSh := PreSheaves( A );
#! PreSheaves( Algebroid( Q, FreeCategory(
#! RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#! Category of matrices over Q )
Y := YonedaEmbedding( A );
#! Yoneda embedding functor
Display( Y );
#! Yoneda embedding functor:
#! 
#! Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#! / relations
#!   |
#!   V
#! PreSheaves( Algebroid( Q, FreeCategory(
#! RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#! Category of matrices over Q )
FreeAbelian := Opposite( FreydCategory( Opposite( PSh ) ) );
#! Opposite of Freyd( Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#! RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#! Category of matrices over Q ) )
a := Opposite( AsFreydCategoryMorphism( Opposite( Y( A.a ) ) ) );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
b := Opposite( AsFreydCategoryMorphism( Opposite( Y( A.b ) ) ) );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
c := Opposite( AsFreydCategoryMorphism( Opposite( Y( A.c ) ) ) );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
d := CokernelProjection( a );
#! <An epimorphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
e := CokernelColift( a, PreCompose( b, c ) );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
f := KernelEmbedding( e );
#! <A monomorphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
g := KernelEmbedding( c );
#! <A monomorphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
h := KernelLift( c, PreCompose( a, b ) );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
i := CokernelProjection( h );
#! <An epimorphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
ff := AsGeneralizedMorphism( f );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
dd := AsGeneralizedMorphism( d );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
bb := AsGeneralizedMorphism( b );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
gg := AsGeneralizedMorphism( g );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
ii := AsGeneralizedMorphism( i );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
ss := PreCompose( [ ff, PseudoInverse( dd ), bb, PseudoInverse( gg ), ii ] );
#! <A morphism in Generalized morphism category of Opposite of Freyd(
#!  Opposite of PreSheaves( Algebroid( Q, FreeCategory(
#!  RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) / relations,
#!  Category of matrices over Q ) )>
IsHonest( ss );
#! true
s := HonestRepresentative( ss );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
j := KernelObjectFunctorial( b, d, e );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
k := CokernelObjectFunctorial( h, g, b );
#! <A morphism in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
HK := HomologyObject( j, s );
#! <An object in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
IsZero( HK );
#! true
HC := HomologyObject( s, k );
#! <An object in Opposite of Freyd( Opposite of PreSheaves(
#!  Algebroid( Q, FreeCategory( RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) )
#!  / relations, Category of matrices over Q ) )>
IsZero( HC );
#! true
#! @EndExample

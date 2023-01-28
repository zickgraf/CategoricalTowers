#! @BeginChunk primitive

LoadPackage( "Algebroids" );

#! @Example
# Hopf algebra generated by a primitive element
q := RightQuiver( "q(1)[t:1->1]" );
#! q(1)[t:1->1]
Q := HomalgFieldOfRationals( );
#! Q
Qq := PathAlgebra( Q, q );
#! Q * q
B := Algebroid( Qq );
#! Algebra( Q, FreeCategory( RightQuiver( "q(1)[t:1->1]" ) ) )
Q = UnderlyingAlgebra( B );
#! true
B2 := B^2;
#! Algebra( Q, FreeCategory(
#! RightQuiver( "qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]" ) ) ) / relations

B0 := B^0;
#! Algebra( Q, FreeCategory( RightQuiver( "*(1)[]" ) ) )

counit_rec := rec( t := 0 );;
comult_rec := rec( t := B2.1xt + B2.tx1 );;
AddBialgebroidStructure( B, counit_rec, comult_rec );
#! Bialgebra( Q, FreeCategory( RightQuiver( "q(1)[t:1->1]" ) ) )

antipode_rec := rec( t:= -B.t );;
AddAntipode( B, antipode_rec );

counit := Counit( B );
#! Functor from Bialgebra( Q, FreeCategory( RightQuiver( "q(1)[t:1->1]" ) ) )
#! ->
#! Algebra( Q, FreeCategory( RightQuiver( "*(1)[]" ) ) )

comult := Comultiplication( B );
#! Functor from Bialgebra( Q, FreeCategory( RightQuiver( "q(1)[t:1->1]" ) ) )
#! ->
#! Algebra( Q, FreeCategory(
#! RightQuiver( "qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]" ) ) ) / relations

idB := IdentityFunctor( B );
#! Identity functor of Algebra( Q, FreeCategory( RightQuiver( "q(1)[t:1->1]" ) ) )

ApplyFunctor( comult, B.t );
#! (1x1)-[{ 1*(tx1) + 1*(1xt) }]->(1x1)

ApplyFunctor( counit, B.t );
#! (1)-[0]->(1)

IsCommutative(B);
#! true

IsCounitary(B);
#! true

IsCocommutative(B);
#! true

IsHopfAlgebroid(B);
#! true

BB := CategoryOfAlgebroidsObject(B);;

IsCoassociative( BB );
#! true

IsCounitary( BB );
#! true


#! @EndExample
#! @EndChunk
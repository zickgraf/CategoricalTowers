#! @Chunk Hom

LoadPackage( "FunctorCategories" );

#! To illustrate our implementation of the category of functors, we consider the following example.
#! First, create a quiver $q$ with one vertex 1 and one edge $t$.

#! @Example
q := RightQuiver( "q(1)[t:1->1]" );
#! q(1)[t:1->1]
#! @EndExample

#! Construct the path algebra $\mathbb{Q}q$ of this quiver over $\mathbb{Q}$.
#! It is isomorphic to the polynomial algebra $\mathbb{Q}[t]$.

#! @Example
Q := HomalgFieldOfRationals( );
#! Q
Qq := PathAlgebra( Q, q );
#! Q * q
#! @EndExample

#! Out of this path algebra construct the algebroid (actually the algebra) $B$ that
#! is obtained as the quotient of the path algebra modulo the ideal $(t^3 - 1)$.

#! @Example
B := Algebroid( Qq, [ Qq.t^3 - Qq.1 ] );
#! Algebra generated by the right quiver q(1)[t:1->1]
RelationsOfAlgebroid( B );
#! [ (1)-[1*(t*t*t) - 1*(1)]->(1) ]
#! @EndExample

#! We define a record that will be used to construct the $\mathbb{Q}$-linear morphism $\epsilon \colon B \to \mathbb{Q}$ defined by $\epsilon(t)=1$.

#! @Example
counit := rec( t := 1 );
#! rec( t := 1 )
#! @EndExample

#! Next we want to construct the $\mathbb{Q}$-linear morphism $\Delta \colon B \to B \otimes_{\mathbb{Q}} B$
#! defined by $\Delta(t)= t \otimes t$. In order to do so, we first need $B \otimes_\mathbb{Q} B$.

#! @Example
B2 := B^2;
#! Algebra generated by the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
#! @EndExample

#! We define a record that will be used to construct $\Delta$.
#! Note that we obtain $t \otimes t$ as the product of the generators $t \otimes 1$ and $1 \otimes t$ of $B \otimes_\mathbb{Q} B$.
#! The order does not matter.

#! @Example
comult := rec( t := PreCompose( B2.tx1, B2.1xt ) );
#! rec( t := (1x1)-[{ 1*(1xt*tx1) }]->(1x1) )
PreCompose(B2.1xt, B2.tx1) = PreCompose(B2.tx1, B2.1xt);
#! true
#! @EndExample

#! Use the records comult and counit to define a bialgebroid (actually a bialgebra) structure on $B$.

#! @Example
AddBialgebroidStructure( B, counit, comult );
#! Bialgebra generated by the right quiver q(1)[t:1->1]
#! @EndExample

#! Extract comultiplication and counit from $B$, now as functors.

#! @Example
counit := Counit( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver *(1)[]
comult := Comultiplication( B );
#! Functor from finitely presented Bialgebra generated by
#! the right quiver q(1)[t:1->1] -> Algebra generated by
#! the right quiver qxq(1x1)[1xt:1x1->1x1,tx1:1x1->1x1]
#! @EndExample

#! We can apply the comultiplication and counit to objects and morphisms of $B$.

#! @Example
ApplyFunctor( counit, B.1 );
#! (1)
ApplyFunctor( counit, B.t );
#! (1)-[1*(1)]->(1)
ApplyFunctor( comult, B.1 );
#! (1x1)
ApplyFunctor( comult, B.t );
#! (1x1)-[{ 1*(1xt*tx1) }]->(1x1)
#! @EndExample

#! Next we define an antipode on $B$ as the (anti)endomorphism on $B$ that sends $t$ to $t^2$.
#! This corresponds to the (anti)endomorphism of the cyclic group of order 3 that sends an element to its inverse.

#! @Example
antipode := rec( t := PreCompose( B.t, B.t ) );
#! rec( t := (1)-[{ 1*(t*t) }]->(1) )

AddAntipode( B, antipode );
antipode := Antipode( B );
#! Contravariant functor from finitely presented
#! Hopf algebra generated by the right quiver q(1)[t:1->1]
#! -> Hopf algebra generated by the right quiver q(1)[t:1->1]
ApplyFunctor( antipode, B.1 );
#! (1)
ApplyFunctor( antipode, B.t );
#! (1)-[{ 1*(t*t) }]->(1)
#! @EndExample

#! Let $A$ be the category of matrices as a skeletal model for the category of finite dimensional vector spaces over $\mathbb{Q}$.
#! Its objects are non-negative integers and its morphisms are matrices with coefficients in $\mathbb{Q}$.

#! @Example
LoadPackage( "LinearAlgebraForCAP" );
#! true
A := MatrixCategory( Q );
#! Category of matrices over Q
#! @EndExample

#! Construct the category $H$ of functors from $B$ to $A$.
#! An object in this category is a pair consisting of a
#! finite-dimensional vector space, specified by its dimension,
#! together with an endomorphism of this vector space, specified by a
#! square matrix.

#! @Example
H := Hom( B, A );
#! The category of functors: Hopf algebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
#! @EndExample

#! Verify that its zero object $z$ behaves as expected.

#! @Example
z := ZeroObject( H );
#! <A zero object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
z( B.1 );
#! <A vector space object over Q of dimension 0>
z( B.t );
#! <A zero, identity morphism in Category of matrices over Q>
idz := IdentityMorphism( z );
#! <A zero, identity morphism in The category of functors: Hopf algebra
#!  generated by the right quiver q(1)[t:1->1] -> Category of matrices over Q>
idz( B.1 );
#! <A zero, identity morphism in Category of matrices over Q>
DirectSum( z, z );
#! <A zero object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
DirectSum( z, z ) = z;
#! true
#! @EndExample

#! Now we construct an object in $H$, i.e. a functor from $B$ to $A$.
#! To this end we need a finite dimensional vector space $V_0$

#! @Example
V0 := VectorSpaceObject( 3, Q );
#! <A vector space object over Q of dimension 3>
#! @EndExample

#! and an endomorphism $\varphi$ on $V_0$.

#! @Example
phi := HomalgMatrix( [ 0, 1, 0,  0, 0, 1,  1, 0, 0 ], 3, 3, Q );
#! <A 3 x 3 matrix over an internal ring>
V := VectorSpaceObject( 3, Q );
#! <A vector space object over Q of dimension 3>
V_obj := rec( 1 := V );
#! rec( 1 := <A vector space object over Q of dimension 3> )
V_mor := rec( t := VectorSpaceMorphism( V, phi, V ) );
#! rec( t := <A morphism in Category of matrices over Q> )
V := AsObjectInHomCategory( B, V_obj, V_mor );
#! <An object in The category of functors: Hopf algebra generated by the
#! right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! Both together can be used to define an object in $H$.

#! @Example
V_obj := rec( 1 := V0 );
#! rec( 1 := <A vector space object over Q of dimension 3> )
V_mor := rec( t := VectorSpaceMorphism( V0, phi, V0 ) );
#! rec( t := <A morphism in Category of matrices over Q> )
V := AsObjectInHomCategory( B, V_obj, V_mor );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! This functor is indeed well defined.

#! @Example
IsWellDefined( V );
#! true
#! @EndExample

#! Let us see how such a functor can fail to be well defined:

#! @Example
psi := HomalgMatrix( [ 1, 0, 0,  0, 0, 1,  0, 1, 0 ], 3, 3, Q );
#! <A 3 x 3 matrix over an internal ring>
W_obj := rec( 1 := V0 );
#! rec( 1 := <A vector space object over Q of dimension 3> )
W_mor := rec( t := VectorSpaceMorphism( V0, psi, V0 ) );
#! rec( t := <A morphism in Category of matrices over Q> )
W := AsObjectInHomCategory( B, W_obj, W_mor );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( W );
#! false
#! @EndExample

#! Display some of the properties of this functor.

#! @Example
V( B.1 );
#! <A vector space object over Q of dimension 3>
V( B.t );
#! <A morphism in Category of matrices over Q>
Display( V( B.t ) );
#! [ [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
IsZero( V );
#! false
#! @EndExample

#! Costruct the direct sum of $V$ with itself.

#! @Example
VoplusV := DirectSum( V, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
VoplusV( B.1 );
#! <A vector space object over Q of dimension 6>
VoplusV( B.t );
#! <A morphism in Category of matrices over Q>
Display( VoplusV( B.t ) );
#! [ [  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  1,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Construct the projection $\pi_1$ from $V \oplus V$ to the first summand and study some of its properties.

#! @Example
pi1 := ProjectionInFactorOfDirectSum( [ V, V ], 1 );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = -pi1;
#! false
pi1( B.1 );
#! <A morphism in Category of matrices over Q>
Display( pi1( B.1 ) );
#! [ [  1,  0,  0 ],
#!   [  0,  1,  0 ],
#!   [  0,  0,  1 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ],
#!   [  0,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
IsWellDefined( pi1 );
#! true
IsEpimorphism( pi1 );
#! true
IsMonomorphism( pi1 );
#! false
#! @EndExample

#! Construct the kernel object $V1$ of $\pi_1$ and check that it is $V$.

#! @Example
V1 := KernelObject( pi1 );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( V1 );
#! true
V1 = V;
#! true
#! @EndExample

#! Construct the projection $\pi_2$ from $V \oplus V$ to the second summand and check that it is not equal to $\pi_1$.

#! @Example
pi2 := ProjectionInFactorOfDirectSum( [ V, V ], 2 );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
pi1 = pi2;
#! false
#! @EndExample

#! Construct another object $U$ in the category of functors from $B$ to $A$.

#! @Example
psi := HomalgMatrix( [ 0, 1,  -1, -1 ], 2, 2, Q );
#! <A 2 x 2 matrix over an internal ring>
U := VectorSpaceObject( 2, Q );
#! <A vector space object over Q of dimension 2>
U_obj := rec( 1 := U );
#! rec( 1 := <A vector space object over Q of dimension 2> )
U_mor := rec( t := VectorSpaceMorphism( U, psi, U ) );
#! rec( t := <A morphism in Category of matrices over Q> )
U := CapFunctor( B, U_obj, U_mor );
#! Functor from finitely presented Hopf algebra generated by
#! the right quiver q(1)[t:1->1] -> Category of matrices over Q
U := AsObjectInHomCategory( U );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
IsWellDefined( U );
#! true
U( B.1 );
#! <A vector space object over Q of dimension 2>
U( B.t );
#! <A morphism in Category of matrices over Q>
Display( U( B.t ) );
#! [ [   0,   1 ],
#!   [  -1,  -1 ] ]
#! 
#! A morphism in Category of matrices over Q
IsZero( U );
#! false
#! @EndExample

#! To construct a morphism $\eta$ from $V$ to $U$ in $H$ (i.e. a natural transformation from the functor $V$ to $U$), we first define a HomAlg matrix.

#! @Example
eta := HomalgMatrix( [ 1, 0,  0, 1,  -1, -1 ], 3, 2, Q );
#! <A 3 x 2 matrix over an internal ring>
#! @EndExample

#! Then we define a record that will be used to define the natural transformation $\eta$.
#! Here `1` is the string representation of the only object of $B$ and the vector space morphism
#! induced by the above matrix is the component of $\eta$ at this object.

#! @Example
eta := rec( 1 := VectorSpaceMorphism( V( B.1 ), eta, U( B.1 ) ) );
#! rec( 1 := <A morphism in Category of matrices over Q> )
#! @EndExample

#! Finally we construct the natural transformation $\eta$ from $V$ to $U$ as a morphism in the category of functors from $B$ to $A$.

#! @Example
eta := AsMorphismInHomCategory( V, eta, U );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
#! @EndExample

#! We check that $\eta$ is well defined.

#! @Example
IsWellDefined( eta );
#! true
#! @EndExample

#! We retrieve the component of $\eta$ at the object 1 of $B$.

#! @Example
eta( B.1 );
#! <A morphism in Category of matrices over Q>
Display( eta( B.1 ) );
#! [ [   1,   0 ],
#!   [   0,   1 ],
#!   [  -1,  -1 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! We study some of the properties of $\eta$.

#! @Example
IsEpimorphism( eta );
#! true
IsMonomorphism( eta );
#! false
#! @EndExample

#! Construct the kernel object of $\eta$.

#! @Example
K := KernelObject( eta );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
K( B.1 );
#! <A vector space object over Q of dimension 1>
K( B.t );
#! <A morphism in Category of matrices over Q>
Display( K( B.t ) );
#! [ [  1 ] ]
#! 
#! A morphism in Category of matrices over Q
iota := KernelEmbedding( eta );
#! <A monomorphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
C := CokernelObject( iota );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
C = U;
#! true
#! @EndExample

#! Since $B$ is a bialgebra, $H$ becomes a monoidal category.
#! First we obtain the unit object $I$ of this monoidal category.

#! @Example
I := TensorUnit( H );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
I( B.1 );
#! <A vector space object over Q of dimension 1>
I( B.t );
#! <A morphism in Category of matrices over Q>
Display( I( B.t ) );
#! [ [  1 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! It turns out that $I$ is equal to $K$.

#! @Example
I = K;
#! true
#! @EndExample

#! Construct the tensor product $V \otimes V$.

#! @Example
VV := TensorProductOnObjects( V, V );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
VV( B.1 );
#! <A vector space object over Q of dimension 9>
VV( B.t );
#! <A morphism in Category of matrices over Q>
Display( VV( B.t ) );
#! [ [  0,  0,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0,  0,  0,  0 ] ]
#! 
#! A morphism in Category of matrices over Q
#! @EndExample

#! Compute the dual object of $U$.

#! @Example
Us := DualOnObjects( U );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Us( B.1 );
#! <A vector space object over Q of dimension 2>
Us( B.t );
#! <A morphism in Category of matrices over Q>
Display( Us( B.t ) );
#! [ [  -1,   1 ],
#!   [  -1,   0 ] ]
#! 
#! A morphism in Category of matrices over Q
epsilon := MorphismToBidual( U );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Source( epsilon ) = U;
#! true
Range( epsilon ) = U;
#! true
EndU := InternalHomOnObjects( U, U );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
UsU := TensorProductOnObjects( Us, U );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
UUs := TensorProductOnObjects( U, Us );
#! <An object in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
EndU = UsU;
#! true
EndU = UUs;
#! false
beta := Braiding( Us, U );
#! <A morphism in The category of functors: Hopf algebra generated by
#!  the right quiver q(1)[t:1->1] -> Category of matrices over Q>
Source( beta ) = UsU;
#! true
Range( beta ) = UUs;
#! true
#! @EndExample

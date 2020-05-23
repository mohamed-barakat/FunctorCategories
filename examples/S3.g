#! @Chunk S3

LoadPackage( "CatReps" );

#! @Example
q := RightQuiver( "q(1)[a:1->1,b:1->1]" );
#! q(1)[a:1->1,b:1->1]
Q := HomalgFieldOfRationals( );
#! Q
Qq := PathAlgebra( Q, q );
#! Q * q
Aoid := Algebroid( Qq, [ Qq.a^2-Qq.1, Qq.b^3-Qq.1, Qq.bab-Qq.a ] );
#! Algebroid generated by the right quiver q(1)[a:1->1,b:1->1]
Qmat := MatrixCategory( Q );
#! Category of matrices over Q
CatReps := Hom( Aoid, Qmat );
#! The category of functors: Bialgebroid generated by the right quiver
#! q(1)[a:1->1,b:1->1] -> Category of matrices over Q
CommutativeRingOfLinearCategory( CatReps );
#! Q
Y := YonedaEmbedding( Aoid );
#! Yoneda embedding functor
V := Y( Aoid.1 );
#! <(1)->6; (a)->6x6, (b)->6x6>
#! @EndExample

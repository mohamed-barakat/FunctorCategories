InstallGlobalFunction( LINEAR_SYSTEM_OF_EXTERNAL_HOM_BETWEEN_TWO_FUNCTORS_INTO_MATRIX_CATEGORY,
  function( F, G )
    local H, kq, kmat, k, A, q, objects, n, morphisms, alpha, beta, gamma, delta, i, mor, source, target;
    
    H := CapCategory( F );
    
    kq := Source( H );
    
    kmat := Range( H );
    
    if not IsMatrixCategory( kmat ) then
        
        Error( "The range category of the input should be a matrix category for some homalg field!\n" );
        
    fi;
    
    k := CommutativeRingOfLinearCategory( kmat );
    
    A := UnderlyingQuiverAlgebra( kq );
    
    q := QuiverOfAlgebra( A );
    
    objects := SetOfObjects( kq );
    n := Length( objects );
    
    morphisms := SetOfGeneratingMorphisms( kq );
    
    alpha := [ ];
    beta := [ ];
    gamma := [ ];
    delta := [ ];

    for i in [ 1 .. Length( morphisms ) ] do
        
        mor := morphisms[i];
        
        source := VertexIndex( UnderlyingVertex( Source( mor ) ) );
        target := VertexIndex( UnderlyingVertex( Range( mor ) ) );
        
        alpha[i] := List( [ 1 .. n ],
          function( j )
            local Fmor;
            
            Fmor := F( mor );
            
            if j = target then
                return Fmor;
            fi;
            
            return ZeroMorphism( Source( Fmor ), F( objects[j] ) );
            
        end );
        
        beta[i] := List( [ 1 .. n ],
          function( j )
            local Gtarget;
            
            Gtarget := G( Range( mor ) );
            
            if j = target then
                return IdentityMorphism( Gtarget );
            fi;
            
            return ZeroMorphism( G( objects[j] ), Gtarget );
            
        end );
        
        gamma[i] := List( [ 1 .. n ],
          function( j )
            local Fsource;
            
            Fsource := F( Source( mor ) );
            
            if j = source then
                return IdentityMorphism( Fsource );
            fi;
            
            return ZeroMorphism( Fsource, F( objects[j] ) );
            
        end );
        
        delta[i] := List( [ 1 .. n ],
          function( j )
            local Gmor;
            
            Gmor := G( mor );
            
            if j = source then
                return Gmor;
            fi;
            
            return ZeroMorphism( G( objects[j] ), Range( Gmor ) );
            
        end );
        
        Assert( gamma[i], List( [ 1 .. Length( alpha[i] ) ],
          function( j )
            local source_alpha_i, range_alpha_ij;
            
            source_alpha_i := Source( alpha[i][1] );
            range_alpha_ij := Range( alpha[i][j] );
            
            if IsEqualForObjects( source_alpha_i, range_alpha_ij ) and
               not IsZero( delta[i][j] ) then
                return IdentityMorphism( source_alpha_i );
            fi;
            
            return ZeroMorphism( source_alpha_i, range_alpha_ij );
            
        end ) );
        
        Assert( beta[i], List( [ 1 .. Length( delta[i] ) ],
          function( j )
            local range_delta_i, source_delta_ij;
            
            range_delta_i := Range( delta[i][1] );
            source_delta_ij := Source( delta[i][j] );
            
            if IsEqualForObjects( range_delta_i, source_delta_ij ) and
               not IsZero( alpha[i][j] ) then
                return IdentityMorphism( range_delta_i );
            fi;
            
            return ZeroMorphism( source_delta_ij, range_delta_i );
            
        end ) );
        
    od;
    
    return [ alpha, beta, gamma, delta ];
    
    #SolveHomogeneousLinearSystemInAbCategory( alpha, beta );
    
end );

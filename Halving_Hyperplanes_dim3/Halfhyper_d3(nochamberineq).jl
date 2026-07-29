using Oscar
using LinearAlgebra
using HomotopyContinuation
using Plots 

# PRE: V is a collection of vertices in R^3 defining a polytope.
# POST: Returns the d-dimensional volume of the polytope spanned by V.
function areaofpolytope(V)
    P = convex_hull(QQ,V)
    return volume(P)
end

# PRE: v is a point in R^3 and h is a vector of coefficients defining the
#      hyperplane H = {x : h · (x,-1) = 0}.
# POST: Returns the evaluation of the hyperplane equation at v, i.e.,
#       h · (v,-1).
function inner_product(v,h)
    S = parent(v[1])
    v_lift = [S(x) for x in v]
    push!(v_lift, -S(1))
    s = sum(h[i]*v_lift[i] for i in 1:length(h))
    return s
end

# PRE: V is a collection of vertices in R^3 defining a polytope.
# POST: Returns the lifted vertices in R^4, where each vertex v is mapped
#       to (v,-1).
function vertex_embed(V)
    embedding = Vector{Vector{QQFieldElem}}()
    for v in V
        #println(v)
        v_lift = copy(v)
        #println(v_lift)
        push!(v_lift,-1)
        push!(embedding,v_lift)
    end
    return embedding
end

# PRE: V is a collection of vertices in R^3 defining a polytope, and h is a
#      vector of coefficients defining the hyperplane
#      H = {x : h · (x,-1) = 0}.
# POST: Returns a vector containing the 2-dimensional faces of the polytope
#       that are intersected by the hyperplane H.
function hyperplane_intersect(V,h)
	P = convex_hull(QQ,V)
	cut = []
    
	for e in faces(P, Oscar.ambient_dim(P)-1)
        #println(e)
		s = [inner_product(collect(v),h) for v in vertices(e)]
        t = 0
        #find the first non-zero value in the vector s
        for i in 1:length(s)
            if s[i] != 0
                t = s[i]
                break
            end
        end
        is_cut = false
        #if there is some value on s of opposite sign as t, push the face into cut
		for r in s
            if (r != 0 && sign(r) != sign(t))
                is_cut = true
                break
            end
        end
        if is_cut
            push!(cut,e)
        end
	end
	return cut #Chiara: this now outputs two edges instead of just the indices of the corresponding vertices
end

    
# PRE: V is a collection of vertices in R^3 defining a polytope, and h is a
#      vector of coefficients defining the hyperplane H = {x : h · (x,-1) = 0}.
# POST: Returns a vector containing the points where H intersects the edges of
#       the polytope spanned by V.
function hyperplane_intersectpoints(V,h)
    facets = hyperplane_intersect(V,h)
    newpoints = Vector{Vector{QQFieldElem}}()
    points = Vector{Vector{QQFieldElem}}()
    for facet in facets
        for f in faces(facet,Oscar.ambient_dim(facet)-2)
            v = [collect(vv) for vv in vertices(f)]
            s1 = inner_product(v[2],h)
            s2 = inner_product(v[1],h)
            if s1 * s2 <= 0 && !(s1 == 0 && s2 == 0)
                l = s1 //(s1 - s2)
                p = [l*v[1][i] + (1-l)*v[2][i] for i in 1:length(v[1])]
                push!(points, p)
            end
        end
    end
    for p in points
        if !(p in newpoints)
            push!(newpoints,p)
        end
    end
return newpoints
end

# PRE: V is a collection of vertices in R^d defining a polytope, and h is a
#      vector of coefficients defining the hyperplane H = {x : h · (x,-1) = 0}.
# POST: Returns the 3-dimensional volume of P(h < 0).
function negative_areaofcut(V,h)
    newpoints = hyperplane_intersectpoints(V,h)
    points = Vector{Vector{QQFieldElem}}()
    for v in V
        s = inner_product(v,h)
        if s < 0
            push!(points, v)        
        end
    end
    for v in newpoints
        push!(points, v)
    end    
    Pplus = convex_hull(QQ, points)
    return(volume(Pplus))
end    


# PRE: V is a collection of vertices in R^3 defining a polytope.
# POST: Returns the maximal chambers (maximal cones) of the hyperplane
#       arrangement induced by the lifted vertices of V.
function get_chambers(V)
    n = length(V)
    embed = vertex_embed(V)
    ha = transpose(reduce(hcat, embed))
    HA = Polymake.fan.HyperplaneArrangement(HYPERPLANES=ha)
    CD = HA.CHAMBER_DECOMPOSITION
    
    fan = polyhedral_fan(CD)
    chambers = maximal_cones(fan)
    return chambers
end


# PRE: V is a collection of vertices in R^3 defining a polytope.
# POST: Returns a representative vector for each maximal chamber of the
#       hyperplane arrangement whose corresponding hyperplane intersects the
#       polytope in a non-empty 2-dimensional section.
function representing_vectors(V)
    chambers = get_chambers(V)
    reprvec = []
    for ch in chambers
        u = sum(rays(ch))
        facecut = hyperplane_intersect(V, u)
        if length(facecut) > 2
            push!(reprvec, (chamber = ch, repr = collect(QQFieldElem, u)))
        end
    end
    return reprvec
end

# PRE: sx is a list of vertices defining a simplex, and S is the fraction field
#      containing the coordinates of the simplex vertices.
# POST: Returns the volume of the simplex using the determinant formula.
function vol_simplex(sx,S)
    n = length(sx)
    columns = [sx[i] - sx[1] for i in 2:n]
    M = reduce(hcat, columns)
    #println(M)
    M_matrix = matrix(S, M)
    volume = Oscar.det(M_matrix)//factorial(n-1)
    return volume
end


# PRE: V is a collection of vertices in R^3 defining a polytope, and h is a
#      representative vector defining the hyperplane
#      H = {x : h · (x,-1) = 0}.
# POST: Returns the numerical and symbolic coordinates of the vertices of the
#       polytope obtained by cutting conv(V) with H. The symbolic coordinates are
#       rational functions in the hyperplane coefficients.
function symbolic_intersection(V,h)
    n = length(V[1])
    variables = ["a$i" for i in 1:n+1]
    P = convex_hull(QQ,V)
    R, vars = polynomial_ring(QQ, variables)
    S = fraction_field(R)

    c = [S(v) for v in vars]
    #this gives the facets getting cut by a hyperplane with coefficients lying in the chamber represented by h
    
    points_num = Vector{Vector{QQFieldElem}}()
    points_sym = Vector{Vector{eltype(S)}}()

     for v in V
        s = inner_product(v,h) 
        if s < 0 #what about = 0?
            push!(points_num, v)
            push!(points_sym, [S(x) for x in v])
        end
    end
        
    for f in faces(P, 1)
        v = [collect(vv) for vv in vertices(f)]
        s1_num = inner_product(v[2],h)
        s2_num = inner_product(v[1],h)

        s1 = inner_product([S(w) for w in v[2]],c)
        s2 = inner_product([S(w) for w in v[1]],c)
        
        if s1_num * s2_num <= 0 && !(s1_num == 0 && s2_num == 0)
            l_num = s1_num //(s1_num - s2_num)
            l_sym = s1 //(s1 - s2)
            
            p_sym = [l_sym*S(v[1][i]) + (1-l_sym)*S(v[2][i]) for i in 1:length(v[1])]
            p_num = [l_num*v[1][i] + (1-l_num)*v[2][i] for i in 1:length(v[1])]
                            
            push!(points_num, p_num)
            push!(points_sym,p_sym)
        end
    end

    return points_num, points_sym, S
end


# PRE: V is a set of vertices defining a polytope in R^3, and h is a
#      representative vector of a chamber in coefficient space.
# POST: Returns a pair containing the numerical volume of the cut polytope for
#       h and the symbolic rational function giving the volume for every
#       hyperplane whose coefficient vector lies in the same chamber as h.
function local_volume(V,h)
    #now we take a look at the points numerically and symbolically
    points_num, points_sym, S = symbolic_intersection(V,h)
    #create a convex hull of the numerical intersection using the representative and take its triangulation 
    Pplus = convex_hull(QQ, points_num)
    #this gives me the indices of the vertices needed
    triang = regular_triangulation(Pplus)

    #now to compute a rational volume function, we create a list of vertices, where the representative intersection 
    #points are substituted by the corresponding functions
    volume_sym = S(0)
    volume_num = QQ(0)
    for index in triang[1]
        sx_num = points_num[index]
        sx_sym = points_sym[index]
        #println(sx)
        volume_num += vol_simplex(sx_num, QQ)
        volume_sym += sign(vol_simplex(sx_num, QQ))*vol_simplex(sx_sym, S)
    end
    volume = (num = volume_num, sym = volume_sym)
    return volume
end


# PRE: V is a collection of vertices in R^d defining a polytope.
# POST: For each chamber of the hyperplane arrangement, returns a rational
#       function describing the volume of the cut polytope for hyperplanes
#       whose coefficient vector lies in that chamber.
function volume_functions(V)
    reprvec = representing_vectors(V)
    functions = []

    for item in reprvec
        h = item.repr
        ch = item.chamber
        
        vol = local_volume(V,h)
        vol_num = vol.num
        vol_sym = vol.sym
        #volume = sign(vol_num)*vol_sym
        
        push!(functions, (chamber = ch, repr = h, local_vol = vol_sym))
    end
    return functions
end

# PRE: V is a set of vertices defining a polytope P in R^3.
# POST: For every chamber, returns the corresponding chamber, a representative
#       vector, and the polynomial equation obtained from the condition that
#       the local volume function equals half of the total volume of P.
function halving_equations(V)
    n = length(V[1])
    variables = ["a$i" for i in 1:n+1]
    R, vars = polynomial_ring(QQ, variables)
    S = fraction_field(R)

    vol_loc = volume_functions(V)
    area = areaofpolytope(V)
    equations = []
    
    for tuple in vol_loc
        ch = tuple.chamber
        fct = tuple.local_vol
        p = numerator(fct)
        q = denominator(fct)
        f = 2*p - area*q
        push!(equations,(chamber = ch, repr= tuple.repr, volume_ch = f ))
    end
    return equations
end

# PRE: f is a polynomial in Oscar with variables vars, i.e. f in k[vars].
# POST: Returns the equivalent polynomial expression in the format required by
#       HomotopyContinuation.
function oscar_to_homcon(f,vars)
    result = HomotopyContinuation.Expression(0)
    n = length(vars)
    for t in terms(f)
        c = collect(AbstractAlgebra.coefficients(t))
        e = collect(AbstractAlgebra.exponent_vectors(t))
        monom = prod(vars[i]^e[1][i] for i in 1:n)
        coeff = numerator(c[1])//denominator(c[1])
        term = Rational(coeff)*monom
        result += term
    end
    return result
end

# PRE: Inputs are three polytopes P, Q, and T in R^3.
# POST: Returns the hyperplane coefficient vectors whose corresponding
#       hyperplanes bisect all three polytopes simultaneously.
function ham_sandwich(P,Q,T)

    V = [collect(v) for v in vertices(P)]
    W = [collect(v) for v in vertices(Q)]
    X = [collect(v) for v in vertices(T)]
    
    n = length(V[1])
    if (length(V) < n || length(W) < n || length(X) < n)
        println("One of the Polygons is degenerate")
        return
    end
    #vogliamo risolvere il sistema di soluzioni usando il metodo dato da homotopycontinuation. Per fare ciò, è importante riuscire a convertire le funzioni da QQMPolyElem a Expression
    Lp = halving_equations(V)
    Lq = halving_equations(W)
    Lt = halving_equations(X)

    half_V= Float64(areaofpolytope(V))/2
    half_W= Float64(areaofpolytope(W))/2
    half_X= Float64(areaofpolytope(X))/2

    @var a b c d
    vars = [a,b,c,d]
    solutions = []

    for p_tuple in Lp
        cp = p_tuple.chamber
        fp = p_tuple.volume_ch
        fp_hc = oscar_to_homcon(fp, vars)
        isempty(variables(fp_hc)) && continue
        
        for q_tuple in Lq
            cq = q_tuple.chamber
            fq = q_tuple.volume_ch
            fq_hc = oscar_to_homcon(fq, vars)
            isempty(variables(fq_hc)) && continue
            
            for t_tuple in Lt
                ct = t_tuple.chamber
                ft = t_tuple.volume_ch
                ft_hc = oscar_to_homcon(ft, vars)
                isempty(variables(ft_hc)) && continue
    
                cc = intersect(intersect(cp, cq), ct)

                if Oscar.dim(cc) > n
                    F = HomotopyContinuation.solve([fp_hc, fq_hc, ft_hc, a^2 + b^2 +c^2 - 1])
                    points = HomotopyContinuation.real_solutions(F) 
                    in_cc = [v for v in points if v in cc]
                    for v in in_cc
                        u = [QQ(rationalize(BigFloat(x))) for x in v]
                        #questa cosa mi fa un po' schif
                        if (abs(Float64(negative_areaofcut(V,u)) - half_V) < 1e-6 &&
                            abs(Float64(negative_areaofcut(W,u)) - half_W) < 1e-6 &&
                            abs(Float64(negative_areaofcut(X,u)) - half_X) < 1e-6 )
                            push!(solutions, v)
                        end
                    end
                end
            end
        end
    end
    return solutions
end


# function main()
#     V1 = [
#     [0, 0, 0],
#     [1, 0, 0],
#     [0, 1, 0],
#     [0, 0, 1]
#     ]
    
#     V2 = [
#     [1, 0, 0],
#     [2, 0, 0],
#     [1, 1, 0],
#     [1, 0, 1]
#     ]
    
#     V3 = [
#     [0, 1, 0],
#     [1, 1, 0],
#     [0, 2, 0],
#     [0, 1, 1]
#     ]
    
    
#     P = convex_hull(QQ, V1)
#     Q = convex_hull(QQ, V2)
#     T = convex_hull(QQ, V3)
#     println(ham_sandwich(P,Q, T))
# end
# main()

function main()
    V_bread = [
        [QQ(-2,1),   QQ(-3,2),   QQ(4,5)],
        [QQ(5,2),    QQ(-4,5),   QQ(4,5)],
        [QQ(-3,10),  QQ(19,10),  QQ(4,5)],
        [QQ(-2,1),   QQ(-3,2),   QQ(1,1)],
        [QQ(5,2),    QQ(-4,5),   QQ(1,1)],
        [QQ(-3,10),  QQ(19,10),  QQ(1,1)]
    ]
    
    # ===== Cream cheese: thin layer, inset ~0.2 units, non-uniform scaling from bread =====
    V_cheese = [
        [QQ(-8,5),   QQ(-33,25), QQ(101,100)],
        [QQ(9,4),    QQ(-4,5),   QQ(101,100)],
        [QQ(-9,25),  QQ(42,25),  QQ(101,100)],
        [QQ(-8,5),   QQ(-33,25), QQ(27,25)],
        [QQ(9,4),    QQ(-4,5),   QQ(27,25)],
        [QQ(-9,25),  QQ(42,25),  QQ(27,25)]
    ]
    
    # ===== Smoked salmon: triangular base, irregular hand-set upper vertices =====
    V_salmon = [
        [QQ(-3,2),   QQ(-23,20), QQ(28,25)],
        [QQ(21,10),  QQ(-1,2),   QQ(28,25)],
        [QQ(-1,4),   QQ(31,20),  QQ(28,25)],
        [QQ(-23,20), QQ(-11,20), QQ(131,100)],
        [QQ(3,4),    QQ(-17,20), QQ(31,25)],
        [QQ(1,20),   QQ(3,4),    QQ(27,20)]
    ]
    P = convex_hull(QQ, V_bread)
    Q = convex_hull(QQ, V_salmon)
    T = convex_hull(QQ, V_cheese)

    area_P = areaofpolytope(V_bread)
    area_Q = areaofpolytope(V_salmon)
    area_T = areaofpolytope(V_cheese)

    println("Area of bread = ", area_P, " ≈ ", Float64(area_P))
    println("Area of salmon = ", area_Q, " ≈ ", Float64(area_Q))
    println("Area of cheese = ", area_T, " ≈ ", Float64(area_T))
    println("Half area of bread = ", area_P // 2, " ≈ ", Float64(area_P // 2))
    println("Half area of salmon = ", area_Q // 2," ≈ ", Float64(area_Q // 2))
    println("Half area of cheese = ", area_T // 2," ≈ ", Float64(area_T // 2))

    solutions = ham_sandwich(P,Q,T)
    println("Ham sandwich solutions: ", solutions)

    for (i, sol) in enumerate(solutions)
        a0 = QQ(rationalize(sol[1]))
        b0 = QQ(rationalize(sol[2]))
        c0 = QQ(rationalize(sol[3]))
        d0 = QQ(rationalize(sol[4]))
        cut_P = negative_areaofcut(V_bread, [a0, b0, c0,d0])
        cut_Q = negative_areaofcut(V_salmon, [a0, b0, c0,d0])
        cut_T = negative_areaofcut(V_cheese, [a0, b0, c0,d0])
        println("\nSolution $i: a=$a0, b=$b0, c=$c0, d =$d0")
        println("  Area cut of P = ", Float64(cut_P), " (target = ", area_P//2," ≈ ",  Float64(area_P//2),")")
        println("  Area cut of Q = ", Float64(cut_Q), " (target = ", area_Q//2," ≈ ",  Float64(area_Q//2),")")
        println("  Area cut of T = ", Float64(cut_T), " (target = ", area_T//2," ≈ ",  Float64(area_T//2),")")
    end
end

main()
using Oscar
using LinearAlgebra
using HomotopyContinuation
using Plots 

#PRE: list of vertices that spans the polytope of which we want to know the area
#POST: returns are of the polytope spanned by "vertices"
function areaofpolytope(V)
    P = convex_hull(QQ,V)
    return volume(P)
end

#PRE: a point v and coefficients a,b,c defining a hyperplane ax+by+c=0
#POST: returns the dot product (a b c). (v 1)
function inner_product(v,a,b,c)
    v_lift = [v[1], v[2], QQ(1)]
    s = dot([a,b,c],v_lift)
    return s
end

#PRE: list of points vertices that spans the polytope, and let a,b,c be the coefficients that describe the hyperplane H={ax+by+c=0}
#POST: returns a vector containing information about the position of each vertex with respect to the hyperplane. Vertices with the same line lie on the same side
function posvertices(V,a,b,c)
    pos = Int[]
    for v in V
        s = inner_product(v,a,b,c)
        push!(pos, sign(s))
    end
    return pos
end

#PRE: list of points vertices that spans the polytope 
#POST: returns the points embedded in R^3
function vertex_embed(V)
    embedding = Vector{Vector{QQFieldElem}}()
    for v in V
        v_lift = [v[1], v[2], QQ(1)]
        push!(embedding,v_lift)
    end
    return embedding
end    

#PRE: list of points vertices that spans the polytope and let a,b,c be the coefficients that describe the hyperplane H={ax+by+c=0}
#POST: returns a vector containing the edges that are cut by the given hyperplane H
function hyperplane_intersectedge(V,a,b,c)
	P = convex_hull(QQ,V)
	cut = []
	for e in faces(P,1)
		s = [inner_product(v,a,b,c) for v in vertices(e)]
		if prod(s) < 0
           		push!(cut, e)
        		end
	end
	return cut #Chiara: this now outputs two edges instead of just the indices of the corresponding vertices
end

    
#PRE: list of points vertices that spans the polytope and let a,b,c be the coefficients that describe the hyperplane H={ax+by+c=0}
#POST: returns a vector containing the exact newpoints where H cuts the polygon spanned by P
function hyperplane_intersectpoints(V,a,b,c)
    edges = hyperplane_intersectedge(V,a,b,c)
    newpoints = Vector{Vector{QQFieldElem}}()
    for e in edges
        v = vertices(e)
        s1 = inner_product(v[2],a,b,c)
        s2 = inner_product(v[1],a,b,c)
        l = s1 //(s1 - s2)
        p = [l*v[1][i] + (1-l)*v[2][i] for i in 1:2]
        push!(newpoints, p)
    end
return newpoints
end

#PRE: list of points vertices that spans the polytope, and let a,b,c be the coefficients that describe the hyperplane H={ax+by+c=0}
#POST: returns the area of the polygon lying above the hyperplane H
function positive_areaofcut(V,a,b,c)
    newpoints = hyperplane_intersectpoints(V,a,b,c)
    points = Vector{Vector{QQFieldElem}}()
    for v in V
        s = inner_product(v,a,b,c)
        if s > 0
            push!(points, v)        
        end
    end
    for v in newpoints
        push!(points, v)
    end    
    Pplus = convex_hull(QQ, points)
    return(volume(Pplus))
end    


#PRE: list of vertices that span the polytope 
#POST: returns the maximal chambers of the calculated hyperplane arrangement
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


#PRE: list of vertices that span the polytope 
#POST: returns one vector for all nonempty maximal chambers of the calculated hyperplane arrangement
function representing_vectors(V)
    chambers = get_chambers(V)
    reprvec = []
    for ch in chambers
        u = sum(rays(ch))
        edgecut = hyperplane_intersectedge(V, u[1],u[2],u[3])
        if length(edgecut) == 2
            #instead of push!(reprvec, u). This converts u from RayVEctor to Vector{QQFieldElem} -> needed?
            push!(reprvec, (chamber = ch, repr = collect(QQFieldElem, u)))
        end
    end
    return reprvec
end


#PRE: V are the vertices of a polytope
#POST: returns the vertices ordered. This might be clockwise or not.
function cyclic_order(V) 
    P = convex_hull(QQ,V)
    g = vertex_edge_graph(P)

    start = 1
    prev  = start
    curr  = neighbors(g, start)[1] # take one neighbor of the starting vertex "start"
    ord   = [start, curr]

    while true
        ns  = neighbors(g, curr)
        # take the next neighbor, not the one we came from
        if ns[1] == prev
            nxt = ns[2]
        else
            nxt = ns[1]
        end
        # check if the next neighbor is your starting point: in that case you are done!
        if nxt == start
            break
        end

        push!(ord, nxt)
        prev, curr = curr, nxt # update and keep going
    end

    return ord
end

##TO IMPROVE, IS NOT OPTIMAL, WORKS ONLY IF VERTICES ARE IN A CYCLIC ORDER##
#PRE: list of vertices that span the polytope 
#POST: returns the area of the spanned polytope without needing to create its convex hull
function shoelace(V)
    n = length(V)
    area = sum(V[i][1]*V[mod(i,n)+1][2] - 
               V[mod(i,n)+1][1]*V[i][2] for i in 1:n)
    return area // 2
end


#PRE: list of vertices that span the polytope, field S and coefficients of the hyperplane a,b,c
#POST: returns the condition of a vertex to be on the same side wrt to the hyperplane ax+by+c=0
function points_above(V,S,a,b,c)
    points = Vector{Vector{eltype(S)}}()
        #using the representing vector, understand which points lie above the hyperplane, so that we can calculate the area cut
    #VL = [[S(v[1]), S(v[2])] for v in V]    
    for v in V
            s = inner_product(v,a,b,c)
            if s > 0
                #push!(points, VL[i])
                push!(points, [S(v[1]), S(v[2])])
            end
        end
    return points
end

    
#PRE: list of vertices that span the polytope 
#POST: returns the regular function that calculates the cut volume for each chamber
function rational_vol_local(V)
    R, (a, b, c) = polynomial_ring(QQ, ["a", "b", "c"])
    S = fraction_field(R)

    fcts = []
    reprvectors = representing_vectors(V)

    for item in reprvectors
        r = item.chamber
        u = item.repr
        edgecut = hyperplane_intersectedge(V, u[1], u[2], u[3])
        
        
        newpoints = Vector{Vector{eltype(S)}}()
        newpoints_eval = Vector{Vector{QQFieldElem}}()
        for e in edgecut
            v = [S.(collect(vv)) for vv in vertices(e)]
            v_eval = [collect(vv) for vv in vertices(e)]
            l = (dot([a, b], v[2]) + c) //(dot([a, b], v[2]) - dot([a, b], v[1]))
            l_eval = inner_product(v_eval[2],u[1], u[2], u[3]) //(inner_product(v_eval[2],u[1], u[2], u[3]) - inner_product(v_eval[1],u[1], u[2], u[3]))
            p = [l*v[1][i] + (1-l)*v[2][i] for i in 1:2]
            p_eval = [l_eval*v_eval[1][i] + (1-l_eval)*v_eval[2][i] for i in 1:2]
            push!(newpoints, p)
            push!(newpoints_eval, p_eval)
        end

        # pts = points_above(V, S, u[1], u[2], u[3])
        push!(newpoints, points_above(V, S, u[1], u[2], u[3])...)
        push!(newpoints_eval, points_above(V, QQ, u[1], u[2], u[3])...)
    
        # now we order the points cyclically, using the evaluated vertices, and we check the sign of the shoelace function
        order = cyclic_order(newpoints_eval)
        sgn = sign(shoelace(newpoints_eval[order]))
    
        local_vol = sgn*shoelace(newpoints[order])
        push!(fcts, (chamber = r, repr =u,  local_area = local_vol))
    end
    return fcts
end

#PRE: Let V be a set of vertices
#POST: returns the representing vector u and its position with respect to the vertices, in other words, we calculate in which chamber u is contained. In altre parole pr ogni camera, calcolo le ineguaglianze che la descrivono, usando il vettore rappresentante
function chambers_conditions(V)
    chmb_sgn = []
    represent = representing_vectors(V)

    for item in represent
        u = item.repr
        sgn_u = []
        for v in V
            #where does u lie with respect to the perpendicular hyperplane spanned by v?
            s = inner_product(v, u[1], u[2], u[3])
            push!(sgn_u, sign(s))
        end
        push!(chmb_sgn, (chamber = item.chamber, repr = u, sgn = sgn_u))
    end

    return chmb_sgn
end


#PRE: Let V be a set of vertices
#POST: returns the representing vector u of each chamber together with the corresponding inequalities. 
function chambers_inequalities(V)
    R, (a, b, c) = polynomial_ring(QQ, ["a", "b", "c"])
    chmb_data = chambers_conditions(V)

    chmb_ineq = []
    for item in chmb_data
        #consider the vector of signs which we calcolare i chambers_conditions(V)
        sgn = item.sgn
        ineq_u = []
        for (i, v) in enumerate(V)
            #for each vertex v=(v1,v2) we multiply the vector of signs of u 
            s = inner_product(v, a, b, c)
            push!(ineq_u, sgn[i] * s)
        end
        push!(chmb_ineq, (chamber = item.chamber, repr = item.repr, inequalities = ineq_u))
    end
    return chmb_ineq
end
    

#PRE: list of vertices that span the polytope 
#POST: returns a vector that contains the equations 2p-Aq=0 where f=p/q is a local expression of the volume (i.e. the equations we need to solve to find the halving hyperplan), together with the corresponding chamber
function halving_equations(V)
    R, (a, b, c) = polynomial_ring(QQ, ["a", "b", "c"])
    S = fraction_field(R)
    vol_loc = rational_vol_local(V)
    area = areaofpolytope(V)
    equations = []
    
    for tuple in vol_loc
        ch = tuple.chamber
        fct = tuple.local_area
        p = numerator(fct)
        q = denominator(fct)
        f = 2*p - area*q
        push!(equations,(chamber = ch, repr= tuple.repr, volume_ch = f ))
    end
    return equations
end

#PRE: The vertices spanning the polygon P
#POST: It returns the chamber with the corrisponding representing vector, the inequalities describing the chamber and the local volume function for vecctors (a,b,c) in that chamber
function halving_hyperplanes(V)
    equations = halving_equations(V)
    inequalities = chambers_inequalities(V)

    relations = []
    for eq in equations
        found = false
        for ineq in inequalities
            if (eq.repr == ineq.repr)
                push!(relations, (chamber = eq.chamber, repr = ineq.repr, equality = eq.volume_ch, ineq = ineq.inequalities))
                found = true
                break
            end
        end
        if !found
            println("Warning: no matching inequalities for repr = ", eq.repr)
        end
    end
    return relations
end


#PRE:A Polynomial f in oscar and the variables vars such that f \in k[vars]
#POST: A polynomial converted to the type HomotopyContinuation
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


#PRE: Inequality and points (a0, b0, c0) 
#POST: Returns tree if (a0, b0, c0) satisfies ineq
function sat_ineq(ineq, a0, b0, c0)
    epsilon = 1e-10
    vars = [a0, b0, c0]
    result = 0.0
    for t in terms(ineq)
        c = collect(AbstractAlgebra.coefficients(t))
        e = collect(AbstractAlgebra.exponent_vectors(t))
        monom = prod(vars[i]^e[1][i] for i in 1:3)
        coeff = numerator(c[1])//denominator(c[1])
        term = Float64(coeff)*monom
        result += term
    end
    return result > -epsilon
end

#PRE: a collection of inequalities cc and a point sol we want to know if it satisfies cc
#POST: returns if sol is contained in the chamber cc
function in_chamber(cc, sol)
    in_chamber = true
    for ineq in cc
        if (!sat_ineq(ineq, sol[1], sol[2], sol[3]))
            in_chamber = false
        end
    end
    return in_chamber
end


#PRE: Inputs are two polytopes P and Q
#POST: The Hyperplanes which cut in half both P and Q
function ham_sandwich(P,Q)
    V = [collect(v) for v in vertices(P)]
    W = [collect(v) for v in vertices(Q)]
    
    if (length(V) < 2 || length(W) < 2)
        println("One of the Polygons is degenerate")
        return
    end
    #vogliamo risolvere il sistema di soluzioni usando il metodo dato da homotopycontinuation. Per fare ciò, è importante riuscire a convertire le funzioni da QQMPolyElem a Expression
    Lp = halving_hyperplanes(V)
    Lq = halving_hyperplanes(W)

    @var a b c
    vars = [a,b,c]
    solutions = []

    for p_tuple in Lp
        for q_tuple in Lq
            #take inequalities of the chamber and the local_area of each
            cp = p_tuple.ineq
            cq = q_tuple.ineq
            fp = p_tuple.equality
            fq = q_tuple.equality

            #convert from type oscar to the right type for HomotopyContinuation
            fp_hc = oscar_to_homcon(fp, vars)
            fq_hc = oscar_to_homcon(fq, vars)

            cc = vcat(cp, cq)
            F = HomotopyContinuation.solve([fp_hc, fq_hc, a^2 + b^2 - 1])
            points = HomotopyContinuation.real_solutions(F)
            for sol in points
                if (in_chamber(cc, sol))
                    push!(solutions, sol)
                end
            end
        end
    end
    return solutions
end

#PRE: Takes the vertices points spanning a polygon
#POST: returns a vector of points (x,y), where v=(x,y) are the vertices of the polygon
function plot_polygon(V)
    P = convex_hull(V)
    verts = vertices(P)
    ord = cyclic_order(verts)
    
    println(verts[ord])
    # verts = vertices(P) 
    # Convert Rational (QQ) to Float64 for the plotting engine
    x_coords = [Float64(v[1]) for v in verts[ord]]
    y_coords = [Float64(v[2]) for v in verts[ord]]
    return (x = x_coords, y = y_coords)
end

#PRE: Take the points spanning two polygons V and W
#POST: gives a plot of the two polygons in R^2
function polygons_inplane(V,W)   
    P = convex_hull(QQ,V)
    Q = convex_hull(QQ,W)
    
    P1 = plot_polygon(V)
    P2 = plot_polygon(W)


    fig = plot(P1.x, P1.y, seriestype=:shape, fillalpha=0.3, label="P", aspect_ratio=:equal, title="Ham Sandwich")
    plot!(fig, P2.x, P2.y, seriestype=:shape, fillalpha=0.3, label="Q")
    scatter!(fig, P1.x, P1.y, color=:red, label="")
    scatter!(fig, P2.x, P2.y, color=:blue, label="")
end

#PRE: Needs the hyperplane given by the coefficients in the vector u and the plot fig we want to complete
#POST: Adds the hyperplane generated by u to the plane containing the polygons
function plot_hyperplane(fig, u)
    x = range(-6, 6, length=100)
    if abs((u[2])) < 1e-10
        println("Division through 0")
        return
    end
    y = [(-u[3] - u[1]*xi)/u[2] for xi in x]
    plot!(fig, collect(x), y, label="halving", color=:green)
end

    
function main()
    n = rand(3:20)
    m = rand(3:20)
    
    rand_frac() = QQ(rand(-5:5)) // QQ(rand(1:5))
    
    V = [[rand_frac(), rand_frac()] for i in 1:n]
    W = [[rand_frac(), rand_frac()] for i in 1:m]

    println("Points of polygon P = ", V)
    println("Points of polygon Q = ", W)
    
    P = convex_hull(QQ, V)
    Q = convex_hull(QQ, W)

    area_P = areaofpolytope(V)
    area_Q = areaofpolytope(W)
    println("Area of P = ", area_P, " ≈ ", Float64(area_P))
    println("Area of Q = ", area_Q, " ≈ ", Float64(area_Q))
    println("Half area of P = ", area_P // 2, " ≈ ", Float64(area_P // 2))
    println("Half area of Q = ", area_Q // 2," ≈ ", Float64(area_Q // 2))

    solutions = ham_sandwich(P, Q)
    println("Ham sandwich solutions: ", solutions)

    for (i, sol) in enumerate(solutions)
        a0 = QQ(rationalize(sol[1]))
        b0 = QQ(rationalize(sol[2]))
        c0 = QQ(rationalize(sol[3]))
        cut_P = positive_areaofcut(V, a0, b0, c0)
        cut_Q = positive_areaofcut(W, a0, b0, c0)
        println("\nSolution $i: a=$a0, b=$b0, c=$c0")
        println("  Area cut of P = ", Float64(cut_P), " (target = ", area_P//2," ≈ ",  Float64(area_P//2),")")
        println("  Area cut of Q = ", Float64(cut_Q), " (target = ", area_Q//2," ≈ ",  Float64(area_Q//2),")")
    end

    # plot
    V_mat = matrix(QQ, V)
    W_mat = matrix(QQ, W)
    P1 = plot_polygon(V_mat)
    P2 = plot_polygon(W_mat)
    
    fig = plot(P1.x, P1.y, seriestype=:shape, fillalpha=0.3, label="P", aspect_ratio=:equal, title="Ham Sandwich")
    plot!(P2.x, P2.y, seriestype=:shape, fillalpha=0.3, label="Q")

    for sol in ham_sandwich(P,Q)
        plot_hyperplane(fig,sol)
    end
    
    scatter!(fig, P1.x, P1.y, color=:blue, label="")
    scatter!(fig, P2.x, P2.y, color=:red, label="")
    display(fig)
    readline()
end
main()



    
    # V = [
    #     [QQ(4), QQ(1)],
    #     [QQ(5), QQ(3)],
    #     [QQ(2), QQ(4)],
    #     [QQ(0), QQ(2)],
    #     [QQ(1), QQ(1)]
    # ]

    # W = [[QQ(0), QQ(1)],
    #     [QQ(1), QQ(0)],
    #     [QQ(1), QQ(1)]]
    # P = convex_hull(QQ,V)
    # Q = convex_hull(QQ,W)

    # println(ham_sandwich(P,Q))

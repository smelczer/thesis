############################################################################################
# Code by Stephen Melczer and Bruno Salvy -- refer to the paper "Symbolic-Numeric
# Tools for Analytic Combinatorics in Several Variables" for details
############################################################################################
DBUG := false:

#####################################################################################################
# Computes a Kronecker representation of the solutions to the system {f = 0 : f in F} where g != 0
# INPUT: 		F - sequence of polynomials forming a regular reduced sequence
#				g - polynomial
#			 vars - ordered list of variables in F and g
#			    u - variable not contained in vars 
#		   useFGb - (optional) Grobner Basis will be calculated with the FGb package if true
#		     linf - (optional) a linear form in vars and u, containing u, to be used
#
# OUTPUT:       T - polynomial in u
#		        Q - list of polynomials in u
#
# The solutions to the the system {f = 0 : f in F} s.t. g != 0 are described by vars[i] = Q[i](u)/T'(u)
# at solutions of T(u)=0.  If linf is not specified then it will be chosen randomly.
#####################################################################################################
Kronecker := proc(F,g,vars,u, useFGb := false, linf := -1) 
	local v, d, h, R, Pd, linform, GB, P, gu, Q, EQ, s,k, T:
	
	# Setup (increase range if needed)
	h := max(map(maxnorm,F));
	d := max(map(degree,F));
	R := rand(-h*d..h*d):

	# Find linear form and compute Gröbner Basis using Rabinowitsch's trick
	if linf = -1 then
		linform := u - add(R()*v,v=vars):
	else
		if degree(linf,u) <> 1 then error "Linear form supplied is not linear in u" fi:
		linform := linf:
	fi:

	if useFGb then 
		GB := FGb[fgb_gbasis]([op(F),linform,1-T*g], 0, [op(vars),T],[u]);
	else
		GB := Groebner['Basis']([op(F),linform,1-T*g],plex(op(vars),T,u));
	fi:
	GB := remove(has,GB,T);

	# Find polynomial P -- take square free part and derivative
	P := remove(has,GB,vars);
	if P=[] then error("Not Zero Dimensional") else P:=op(P) fi;

	P := primpart(normal(P/ gcd(P,diff(P,u))));
	Pd := diff(P,u);

	# Find Q_i for each variable
	for v in vars do
  		EQ := select(has,GB,v);
  		if nops(EQ)<>1 then error("Not Regular Reduced (try again for different linear form)"); fi;
  		EQ := op(EQ);
  		if degree(EQ,v)>1 then error("Not Regular Reduced (try again for different linear form)"); fi;
  		Q[v] := rem(Pd*solve(EQ,v), P, u):
	od:

	if DBUG and map(rem,numer(eval(F,[seq(v=Q[v]/Pd,v=vars)])),P,u)<>[seq(0,k=F)] then
		error "bug in Kronecker",args,P,[seq(Q[v],v=vars)] fi;
	return P, [seq(Q[v],v=vars)]
end:


##########################################################################################################
# Simple code for Newton Iteration
# INPUT: 		f - univariate polynomial in u
#				r - initial approximation of the root
#		        u - variable
#		    kappa - specification of precision
#
# OUTPUT:       x - result of Newton Iteration until |u_n - u_{n+1}| < 10^{-kappa}
#
# Throws an error if no convergence by 2*kappa iterations
###########################################################################################################
NewtonRefine := proc(f,r,u,kappa) local x,y,N,tol,g,boundnbsteps;
  x := r: y := r+1: N := 0: 
  u := op(indets(f));
  tol := Float(1,-kappa);
  g := unapply(u-f/diff(f,u),u);
  boundnbsteps:=2*kappa;
  
  for N to boundnbsteps while (abs(x-y) > tol) do
    y := x:
    x := evalf(g(y)):
  od:

  if (N = boundnbsteps + 1) then error "Did not converge",args fi;
  return x:
end:


##########################################################################################################
# Computes a numerical Kronecker representation of the system represented by P(u)=0, vars[i]=Q[i](u)/P'(u)
# INPUT: 		P - polynomial in the variable u
#				Q - list of polynomials in the variable u
#			 vars - ordered list of variables
#			    u - variable (not contained in vars) 
#		    cmplx - if true returns all complex solutions of P(u)=0, otherwise returns only real solutions
#
# OUTPUT:       U - list of floating point approximations of roots of P
#		        N - list of nops(vars) floating point numbers
#			kappa - precision (in digits) to which the solutions of P are calculated
#
# The entry N[i][j] describes the value of vars[j] at the solution u=U[i] of P(u). Entries of N that are zero
# will be returned as exactly 0, and entries which are equal will be returned as the same floating point numbers
###########################################################################################################
NumericalKronecker := proc(P,Q,vars,u,cmplx:=false) 
	local n, i, j, k, d, U, kappa, Pd, Pdk, N, R, Dig, DigQ, Pdm, Qm, G, UG, Umax, Ureal, q, T, r:
	
	n := nops(vars):
	d := degree(P):
	Pd := diff(P,u):

	# Precision which separates roots of P
	Dig := d^((d+2)/2)*norm(expand(P),2)^(d-1);

	# Get initial approximation to the roots using standard Maple Digits (default = 10)
	if cmplx then
		U := [fsolve(P,u,complex)]:
		Ureal := [fsolve(P,u)]:
		if nops(U)<>d then error "problem with fsolve",P fi
	else
		U := [fsolve(P,u)]:
	fi:
	if U=[] then return [],[],1 fi;

	# Get initial parametrizations for zero coordinates using standard Maple Digits (default = 10)
	for k from 1 to n do
		G[k] := primpart(gcd(P,Q[k]));
		if cmplx then
			UG[k] := [fsolve(G[k],u,complex)]:
		else
			UG[k] := [fsolve(G[k],u)]:
		fi:
	od:

	# Find digits needed for root separation of variables 
	# Calculates unnecessary resultants
	for k from 1 to n do
		R[k] := primpart(resultant(Pd*T-Q[k],P,u));
		R[k] := expand(normal( R[k]/gcd(R[k],diff(R[k],T)) ));
		DigQ[k] := d^((d+2)/2)*norm(R[k],2)^(d-1) + 5;
	od:

	# To decide equality / exact zeroes, sufficient to know Q_j/P' to precision
	Dig := ceil(log[10]( max(Dig,seq(DigQ[k],k=1..n)) )):

	# Use floating point approximations to get bounds on |Q_j-a|,|P'-b|
	# Here |a|/|b| is approximately bounded by 2*|Q_j|/|P'| -- need 10^(-Dig) < |Q_j|/2 and |P'|/2
	Pdm := floor(min(seq(abs(subs(u=k,diff(P,u))),k=U)));
	Qm := ceil(max(seq(seq(abs(subs(u=r,Q[k])),r=U),k=1..n)));

	# If |Q_j-a|,|P'-b| < 10^(-k) then |Q/P'-a/b| < 10^(-k)/|P'|*(1+|a|/|b|)
	# Thus we need to find P' and Q_j to precision
	Dig := Dig + ceil(log[10]( 1/Pdm + 2*Qm/Pdm^2 ));

	# CIF implies |f(z)-f(a)| <= |z-a|*max(|f'(w)|: |w-a|<=|z-a|) -- we can bound |f'(z)| <= |f'|(|a|+1) when |z-a|<1
	# So we need to find the solutions of P(u) = 0 to precision
	Umax := max(1,map(abs,U));
	kappa := add(abs(coeff(Pd,u,k))*(Umax+1)^k,k=0..degree(Pd,u)):
	kappa := ceil(log[10]( max(1, kappa, seq(add(abs(coeff(q,u,k))*(Umax+1)^k,k=0..degree(q,u)), q=Q) ) )):
	kappa := kappa + Dig:

	# Increase Digits to the necessary precision (does *not* affect global Digits variable)
	# Add a bit extra for space
	Digits := 2*kappa:

	# Refine the solution of P to the necessary precision via Newton Iteration
	U:=map2(NewtonRefine,P,U,u,kappa);

	# Make sure real solutions are recognized as real
	if cmplx then
		Ureal:=map2(NewtonRefine,P,Ureal,u,kappa);
		for k from 1 to nops(Ureal) do
			for j from 1 to nops(U) do
				if (abs(Ureal[k]-U[j]) < evalf(1/(d^((d+2)/2)*norm(expand(P),2)^(d-1)))) then U[j] := Ureal[k]: break: fi:
			od:
		od:
	fi:

	# Find the value of the variables at these solutions
	for k from 1 to nops(U) do
		Pdk := subs(u=U[k], Pd);
		N[k] := [seq( subs(u=U[k],Q[j])/Pdk,j=1..n )]
	od:

	# Find equal coordinates and exact zero coordinates
	for k from 1 to n do
		for i from 1 to nops(U) do 
			if abs(N[i][k]) < 1/(1+maxnorm(R[k])) then N[i][k] := 0: fi:
			for j from i+1 to nops(U) do
				if abs(N[i][k]-N[j][k]) < evalf(1/DigQ[k]) then N[j][k] := N[i][k] fi:
			od:
		od:
	od:

	return U, [seq(N[k],k=1..nops(U))], kappa;
end:


##########################################################################################################
# Calculates the reduction of a rational function with respect to a Kronecker system.
# It is assumed that the denominator does not vanish on the solutions of the system.
#
# INPUT: 		F - rational function in vars
#				P - polynomial in u
#				Q - list of polynomials in u s.t. (P,Q) defines a Kronecker system
#			 vars - ordered list of variables
#			    u - variable (not contained in vars)
#
# OUTPUT:       Qf - Polynomial in u
#				
# 
#	P'*F(vars)-Qf(u) = 0 at the solutions to the Kronecker system defined by (P,Q)
###########################################################################################################
KroneckerReduce := proc(F,P,Q,vars,u) 
	local s,Pdinv,denF,k:
	denF:=denom(F);
	gcdex(P,diff(P,u),u,'s','Pdinv');
	
	if denF<>1 then
		denF:=rem(subs( {seq(vars[k]=Q[k]*Pdinv,k=1..nops(vars))}, denF),P,u);
		gcdex(denF,P,u,'denF','s')
	fi;
	return rem( diff(P,u) * denF * subs( {seq(vars[k]=Q[k]*Pdinv,k=1..nops(vars))}, numer(F)), P, u)
end:


##########################################################################################################
# Finds Asymptotics of Diagonal Coefficient of Rational Function F = G/H assuming that F is combinatorial,
# has a finite number of critical points, has a minimal critical point, and its minimal critical points are 
# non-degenerate
#
# INPUT: 		G - Polynomial (numerator)
#				H - Polynomial (denominator)
#			 vars - ordered list of variables
#			    u - variable (not contained in vars)
#				k - name for the index of the coefficients in the resulting formula
#		   useFGb - flag -- Grobner Basis will be calculated with the FGb package if true
#		     linf - (optional) a linear form in vars and u, containing u, to be used
#		       vt - (optional) a variable not included in {vars,u} to test minimality w/ H(vt*vars)=0
#
# OUTPUT:       P - Minimal polynomial of algebraic numbers in dominant asymptotics
#				U - List of floating point approximations of roots of P giving asymptotics
#			  ASM - Formula of the form T(u)^k * k^alpha * C(u)
#				
#
# The dominant asymptotics of [t^k] DIAG(G/H) are obtained by summing ASM(u) at the roots of P uniquely
# determined by the elements of U
###########################################################################################################
DiagonalAsymptotics := proc(G,H,vars,u,kk, useFGb := false, linf := -1, vt := -1) 
	local T, varsT, sys, P, Q, C, U, R, kappa, kappa2, Pt, Pd, inv, n, cand, minp, pt, torus, refine;
	local Hes, ts, a, s, k, d, tol, Rt, Rexact, Rpos, Ut, Uexact, M, Dig, Tmax, modBound, lambda, t, newP, newPd, invPd, j, v:

	# Check if variable vt provided, and update t if so
	if vt <> -1 then
		if not type(vt,'symbol') then error "Argument vt must be a variable";
		elif (vt in vars) or (vt=u) then error "Argument vt must be distinct from the vars and u";
		else t := vt: fi:
	fi:
	if not (indets(linf) subset {op(vars),u,vt}) then error "Linear form specified has variables not passed to function"; fi;

	n := nops(vars):
	sys := expand([H,seq(v*diff(H,v)-lambda,v=vars),subs({seq(v=v*t,v=vars)},H)]):
	varsT := [op(vars),lambda,t]:
	P,Q := Kronecker(sys,lambda,varsT,u, useFGb, linf):
	U,R, kappa := NumericalKronecker(P,Q,varsT,u,false):
	Pd := diff(P,u);

	# Increase Digits to required precision
	Digits := 2*kappa:

	# Get factor of P corresponding to t <> 1
	newP:=gcd(Pd-Q[n+2],P);
	Pt := primpart(normal(P/newP));
	tol := evalf(1/(maxnorm(Pt)+1));

	# Get roots of P corresponding to exact critical points (t=1)
	Ut,Uexact := selectremove(a->abs(subs(u=a,Pt)) < tol, U);
	if nops(Uexact)=0 then error "No real critical point", args fi;

	# Find Rt corresponding to Ut
	Rexact := seq(R[k],k=[map(ListTools['Search'],Uexact,U)]);
	Rt := seq(R[k],k=[map(ListTools['Search'],Ut,U)]);

	# Find real positive points
	Rpos := select(a->(a[1..n]=map(abs,a[1..n])),Rexact);

	# Find positive minimal critical point
	minp := -1:
	for cand in Rpos do
		# Get values of t corresponding to the point cand
		ts := [seq(pt[n+2], pt=select(a->a[1..n]=cand[1..n],Rt))];
		if nops(select(a->(a>0) and (a<1), ts)) = 0 then minp := cand: break: fi:
	od:
	if (minp=-1) then error "No minimal real critical point", args; fi:

	# We have found the minimal critical point, and reduce the resolution to that part
	newPd:=diff(newP,u);
	gcdex(Pd,newP,u,'invPd');
	Q:=map(rem,[seq(a*newPd*invPd,a=Q)],newP,u);
	P:=newP;
	Pd:=newPd;

	# Find annihilating polynomials of coordinates
	for k from 1 to n do
		M[k] := primpart(resultant(Pd*T-Q[k],P,u));
		M[k] := expand(normal( M[k]/gcd(M[k],diff(M[k],T)) ));
		d := degree(M[k]);

		# Need to know M_k(T) to this accuracy:
		modBound[k] := ((d^2+1)*maxnorm(M[k])^2)^(d^2-1)* (maxnorm(M[k])*d)^(2*d^2);

		# For this we need to know T to this accuracy
		Tmax := max(map(abs, [seq(a[k],a=R)] ));
		Dig[k] := modBound[k] * add(abs(coeff(M[k],T,a))*(Tmax+1)^a,a=0..degree(M[k],T));
	od:

	# Increase to precision needed for Lemma 3.6
	kappa2 := max(kappa,seq(ceil(log[10](Dig[k])),k=1..n));
	Digits := 2*kappa2;
	
	# Find other critical points on same torus
	# Check if abs(abs(x[k])-abs(minp[k])) are less than the root separation bound involving kappa
	torus := [U[ListTools['Search'](minp,R)]];
	cand := select(a->`and`(seq( abs(abs(a[k])-abs(minp[k])) < evalf(10^(-kappa)), k=1..n)), Rexact);
	cand := remove(`=`,cand,minp);

	for k in cand do
		# Refine candidates via Newton
		refine := [seq(NewtonRefine(M[j],k[j],T,kappa2), j=1..n)];
		# Verify M[k](|x|)*M[k](-|x|) < 1/modBound[k]
		if `and`(seq( abs(subs(T=abs(refine[j]),M[j])*subs(T=-abs(refine[j]),M[j])) < evalf(1/modBound[j]), j=1..n)) then 
			torus := [op(torus),U[ListTools['Search'](k,R)]]; 
		fi;
	od:
	
	# Find exponential growth 
	T := KroneckerReduce(convert(vars,`*`),P,Q,vars,u);

	# Find constant (recall lambda = z_n * diff(H,z_n))
	# P' in numerator and denominator cancel out
	gcdex(P,Q[n+1],u,'s','inv');
	C := KroneckerReduce(-G/lambda,P,Q,varsT,u);

	# Find the Hessian
	Hes := DetHessian(H,P,Q,varsT,u);

	# Return the asymptotics
	return (Pd/T)^kk * kk^((1-n)/2) * (2*Pi)^((1-n)/2)* (Pd/Hes)^(1/2) * C/Pd, [seq(RootOf(P,k),k=torus)]:
end:

##########################################################################################################
# Computes the the determinant of the Hessian of the map z_1*...*z_{n-1}*g(z_1,...,z_{n-1}),
# with g defined by the implicit function theorem from H(z_1,...,z_{n-1},g(z_1,...,z_{n-1}))
# assuming that z_n lets us do that.
# The value returned is a rational function in z_1,...,z_{n-1} that gives the value of the 
# determinant of the Hessian at a critical point if evaluated there.
#
# INPUT:		H - Polynomial (denominator)
#				P - polynomial in u
#				Q - list of polynomials in u s.t. (P,Q) defines a Kronecker system
#			varsT - ordered list of variables
#			    u - variable (not contained in vars)
#
# OUTPUT:    detH/z[n]^2 - a polynomial in u s.t. detH(u)/P'(u) is the answer
###########################################################################################################

DetHessian:=proc(H,P,Q,varsT,u)
local n, U, matH,v1,v2,phi,i,vars,j,lambda,detH,prefact,invPd;
	vars:=varsT[1..-3];
	n:=nops(vars);
	lambda:=varsT[-2];

	# Build matrix of second derivatives
	U:=Matrix([seq([seq(v1*v2*diff(H,v1,v2),v2=vars)],v1=vars)]);

	# Build Hessian
	matH:=Matrix([seq([seq(U[i,n]+U[j,n]-U[i,j]-U[n,n]-lambda,j=1..n-1)],i=1..n-1)]);
	for i to n-1 do matH[i,i]:=matH[i,i]-lambda od;
	matH:=map(KroneckerReduce,matH,P,Q,varsT,u);

	# Find determinant and reduce
	gcdex(diff(P,u),P,u,'invPd');
	phi:=convert(vars,`*`);
	prefact:=KroneckerReduce(1/lambda^(n-1),P,Q,varsT,u);
	detH:=prefact*invPd^(n)*LinearAlgebra['Determinant'](matH);
	rem((-1)^(n+1)*diff(P,u)*detH,P,u)
end:


############################################################################
# The following code fixes an error in the Maple 'allvalues' function which 
# causes it to select the wrong root in a RootOf expression
############################################################################
kernelopts(opaquemodules=false):
allvalues:-Closest := proc(sol, a)
local s, tm, d, d2, t, e;
    s := sol[1];
    d := abs(evalf(a - s, max(10, Digits)));
    for tm in sol[2 .. nops(sol)] do d2 := abs(evalf(a - tm, max(10, Digits))); if d2 < d then d:=d2; s := tm elif d2 = d then s := s, tm end if
    end do;
    s := [s];
    if 1 < numelems(s) then
        t := map(x -> [evalf(x, max(10, Digits)), x], s);
        t := sort(t, 'key' = (x -> x[1]));
        d, s := op(t[1]);
        for e in t[2 .. ()] do if not verify(d, e[1], 'boolean'('float'(1))) then d := e[1]; s := s, e[2] end if end do;
        s := [s]
    end if;
    s := map(tm -> `if`(tm::function and op(0, tm) = RootOf, RootOf(op(1, tm), a), tm), s);
    s := ListTools:-MakeUnique(s);
    return s
end proc:
kernelopts(opaquemodules=true):






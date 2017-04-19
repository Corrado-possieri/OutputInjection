-- -*- coding: utf-8 -*-
-- OutputInjectionPackage.m2
-- Copyright (C) 2017  Laura Menini, Corrado Possieri, Antonio Tornambe

-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 3 of the License, or (at
--  your option) any later version.
--
--  This program is distributed in the hope that it will be useful, but
--  WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  General Public License for more details.
--
--  You should have received a copy of the GNU General Public License along
--  with this program; if not, see <http://www.gnu.org/licenses/>.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newPackage (
 "OutputInjection",
 Version => "1.0",
 Date => "Mar 24, 2017",
 Headline => "A set of tools to compute an immersion that recast a nonlinear  
  system into a linear one up to an output injection",
 Authors => {
 {Name => "Laura Menini, Corrado Possieri, Antonio Tornambe", 
  Email => "possieri@ing.uniroma2.it"}
 }
)

-- list of exported functions
export {
 "allEmbed",
 "allEmbedtr",
 "obsForm",
 "obsFormNI",
 "immObs",
 "immObstr",
 "immObsNI",
 "immObstrNI",
 "approxSolODE",
 "compMatr",
 "solveSystem",
 "rationalize",
 "immObstrNum"
}

-- list of exported variables
y := getSymbol "y";
z := getSymbol "z";
t := getSymbol "t";
k := getSymbol "k";
eps := getSymbol "eps";
a := getSymbol "a";
b := getSymbol "b";

-- source code
     
allEmbed = (R,f,h,N) -> (
 -- compute the set of all the embeddings of order N of the system
 -- dot{x} = f(x), y = h(x)
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix.
 
 -- output: the set of all the embeddings of order N,
 --         the observability map of order N of the system.
 
 -- define the variables and the coefficient field
 nVars := vars R;
 n := numColumns nVars;
 coeffR := coefficientRing R;
 
  -- define the new polynomial ring
 R2 := coeffR[nVars_(0,0)..nVars_(0,n-1),y_0..y_N, MonomialOrder => Eliminate n];
 nVars2 := vars R2;
 ylist := new List from (nVars2_(0,n))..(nVars2_(0,n+N));
 
 -- construction of the N-th observability ideal
 Lf := substitute(h,R2);
 I := ideal(0);
 G := 0;
 for ii from 0 to N do (
  -- define the observation ideal of order ii ...
   I = I + ideal(ylist_ii - Lf);
    
  -- update Lf
  LLf := 0;
  for jj from 0 to n-1 do (
   avar := substitute(nVars_(0,jj),R2);
   LLf = LLf + diff(avar,substitute(Lf,R2))*substitute(f_(jj,0),R2);
  );
  Lf = LLf;
 ); 

 -- compute the gb of I
 G = transpose gens gb eliminate(I,toList(substitute(nVars_(0,0),R2)
        ..substitute(nVars_(0,n-1),R2)));
 
 -- return such a gb 
 (G,submatrix'(transpose gens I,{0},{}))
)

allEmbedtr = (R,f,h,N,d) -> (
 -- compute the set of all the d-truncated embeddings of order N of the system
 -- dot{x} = f(x), y = h(x)
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree d of the truncation.
 
 -- output: the set of all the embeddings of order N,
 --         the set of all the d truncated embeddings of order N,
 --         the observability map of order N of the system.
 
 -- use the procedure allEmbed to compute the set of all the embeddings of order N
 GI := allEmbed(R,f,h,N);
 
 -- define the new polynomial ring
 nVars := vars R;
 n := numColumns nVars;
 coeffR := coefficientRing R;
 R2 := coeffR[nVars_(0,0)..nVars_(0,n-1),y_0..y_N, eps, MonomialOrder => Eliminate n];
 nVars2 := vars R2;
 ylist := new List from (nVars2_(0,n))..(nVars2_(0,n+N));
 epp := nVars2_(0,n+N+1);
 G := substitute(GI#0,R2);
 I := substitute(GI#1,R2);
 
 -- the Taylor approximations are used to compute the truncated embeddings
 -- substitute to the y's the variable e*y
 mG := new MutableMatrix from G;
 for ii from 0 to N do (
  for jj from 0 to numRows G - 1 do (
   mG_(jj,0) = substitute(mG_(jj,0), {ylist_ii => epp*ylist_ii});
  );
 );
 
 -- keep just the terms that have degree lower than or equal to d
 nG := new MutableMatrix from 0*G;
 for jj from 0 to numRows nG -1 do (
  par := mG_(jj,0); 
  for ii from 0 to d do (
   nG_(jj,0) = nG_(jj,0) + substitute(par, epp => 0);
   par = diff(epp,par)/(ii+1);
  );
 );
 nG = new Matrix from nG;
 
 -- return the truncated basis
 (G,nG,I) 
)

obsForm = (ell) -> (
 -- compute the embedding of the generic system in linear up to an
 -- output feedback form, with output transformation
 
 -- input: the degree ell of the system.
 
 -- output: the embedding of the system.
 
 -- define the ring of the variables involved in the computations
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := lz + length kvars;
 tvars := new List from t_0..t_ell;
 lt := lk + length tvars;
 yvars := new List from y_0..y_ell;
 ly := lt + length yvars;
 
 AVars := zvars | kvars | tvars | yvars;
 
 S := QQ[AVars];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 kvars = new List from (nVars_(0,lz+1))..(nVars_(0,lk));
 -- print kvars;
 tvars = new List from (nVars_(0,lk+1))..(nVars_(0,lt));
 -- print tvars;
 yvars = new List from (nVars_(0,lt+1))..(nVars_(0,ly));
 -- print yvars;
 
 -- build the vector field and the output map
 ff := new MutableMatrix from 0*random(S^ell,S^1);
 for ii from 0 to ell - 2 do (
  ff_(ii,0) = zvars_(ii+1) + kvars_((ii)*ell);
 );
 ff_(ell-1,0) = kvars_((ell-1)*ell);
 
 ff = new Matrix from ff;
 
 -- print ff;
 
 hh := substitute(tvars_0,S);
 
 -- construction of the corresponding observability ideal
 obsId := new MutableList from 1..ell+1;
 
 phh := hh;
 zlist := new List from zvars;
 
 for ii from 0 to ell do (
  obsId#ii = yvars_ii - phh;
  nphh := 0;
  for jj from 0 to length(zlist) - 1 do (
   nphh = nphh + diff(zlist#jj,phh)*ff_(jj,0);
  );
  for jj from 0 to length kvars - 2 do (
   nphh = nphh + diff(kvars_(jj),phh)*kvars_(jj+1)*(ff_(0,0));
  );
  for jj from 0 to ell - 1 do (
   nphh = nphh + diff(tvars_jj,phh)*tvars_(jj+1)*(ff_(0,0));
  );
  phh = nphh;
 );
 obsId = new List from obsId;
 observationId := ideal(obsId);
 
 -- compute the embedding from the observation ideal
 G := transpose gens gb eliminate(observationId,zlist);
 
 -- return the embedding and the ideal
(G, transpose gens observationId)
)

obsFormNI = (ell) -> (
 -- compute the embedding of the generic system in linear up to an
 -- output feedback form, without output transformation
 
 -- input: the degree ell of the system.
 
 -- output: the embedding of the system.
 
 -- define the ring of the variables involved in the computations
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := lz + length kvars;
 tvars := new List from t_0..t_ell;
 lt := lk + length tvars;
 yvars := new List from y_0..y_ell;
 ly := lt + length yvars;
 
 AVars := zvars | kvars | tvars | yvars;
 
 S := QQ[AVars];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 kvars = new List from (nVars_(0,lz+1))..(nVars_(0,lk));
 -- print kvars;
 tvars = new List from (nVars_(0,lk+1))..(nVars_(0,lt));
 -- print tvars;
 yvars = new List from (nVars_(0,lt+1))..(nVars_(0,ly));
 -- print yvars;
 
 -- build the vector field and the output map
 ff := new MutableMatrix from 0*random(S^ell,S^1);
 for ii from 0 to ell - 2 do (
  ff_(ii,0) = zvars_(ii+1) + kvars_((ii)*ell);
 );
 ff_(ell-1,0) = kvars_((ell-1)*ell);
 
 ff = new Matrix from ff;
 
 -- print ff;
 
 hh := substitute(zvars_0,S);
 
 -- construction of the corresponding observability ideal
 obsId := new MutableList from 1..ell+1;
 
 phh := hh;
 zlist := new List from zvars;
 
 for ii from 0 to ell do (
  obsId#ii = yvars_ii - phh;
  nphh := 0;
  for jj from 0 to length(zlist) - 1 do (
   nphh = nphh + diff(zlist#jj,phh)*ff_(jj,0);
  );
  for jj from 0 to length kvars - 2 do (
   nphh = nphh + diff(kvars_(jj),phh)*kvars_(jj+1)*(ff_(0,0));
  );
  for jj from 0 to ell - 1 do (
   nphh = nphh + diff(tvars_jj,phh)*tvars_(jj+1)*(ff_(0,0));
  );
  phh = nphh;
 );
 obsId = new List from obsId;
 observationId := ideal(obsId);
 
 -- compute the embedding from the observation ideal
 G := transpose gens gb eliminate(observationId,zlist);
 
 -- return the embedding and the ideal
 (G, transpose gens observationId)
)

immObs = (R,f,h,N,ell) -> (
 -- compute the immersion of a nonlinear system  of the form
 -- dot{x} = f(x), y = h(x)
 -- into a linear one up to an output injection with change of
 -- coordinates of the output
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree ell of the immersion.
 
 -- output: a set of DAE to be solved to obtain the injection,
 --         the change of coordinates in implicit form.
 
 -- compute the set of all the embeddings of the system
 ss := allEmbed(R,f,h,N);
 
 -- compute the observability form of order ell
 vv := obsForm(ell);
 
 -- variables and coefficient rings
 coeffR := coefficientRing R;
 xx := gens R;
 n := length(xx);
 mm := numRows ss#0;
 
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 xvars := new List from xx_(0)..xx_(n-1);
 lx := lz + length xvars;
 y0vars := new List from y_0..y_0;
 ly0 := lx + length y0vars;
 avars := new List from a_0..a_(mm-1);
 la := ly0 + length avars;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := la + length kvars;
 tvars := new List from t_0..t_ell;
 lt := lk + length tvars;
 yvars := new List from y_1..y_ell;
 ly := lt + length yvars;
 
 AVars := zvars | xvars | y0vars | avars | kvars | tvars | yvars;
 
 S := QQ[AVars, MonomialOrder => Lex];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 xvars = new List from (nVars_(0,lz+1))..(nVars_(0,lx));
 -- print xvars;
 y0v := nVars_(0,lx+1);
 -- print y0v;
 avars = new List from (nVars_(0,ly0+1))..(nVars_(0,la));
 -- print avars;
 kvars = new List from (nVars_(0,la+1))..(nVars_(0,lk));
 -- print kvars;
 tvars = new List from (nVars_(0,lk+1))..(nVars_(0,lt));
 -- print tvars;
 yvars = new List from (nVars_(0,lt+1))..(nVars_(0,ly));
 -- print yvars;
 
 -- construct the generic embedding of the nonlinear system
 pp := 0;
 for ii from 0 to mm - 1 do (
  pp = pp + avars_ii*substitute((ss#0)_(ii,0),S);
 );
 qq := substitute((vv#0)_(1,0),S);
 
 -- minimum between N and ell
 Nellmin := min({N,ell});
 
 -- construction of the observability map
 obId1 := submatrix(substitute(ss#1,S),new List from 0..(Nellmin-1),{0});
 obId2 := submatrix(substitute(vv#1,S),new List from 0..(Nellmin-1),{0});
 
 -- find the set of equalities that has to be solved
 ylist := new List from yvars;
 (mons,coeffs) := coefficients(pp - qq, Variables => ylist);
 
 -- compute a Groebner basis of the equalities
 idcoeff := ideal(coeffs) + ideal(y0v-tvars_0); 
 G := transpose gens gb (idcoeff);
 
 -- return the Groebner basis and the equalities
 (G,obId1-obId2)
)

immObstr = (R,f,h,N,ell,d) -> (
 -- compute an approximate immersion of a nonlinear system  of the form
 -- dot{x} = f(x), y = h(x)
 -- into a linear one up to an output injection with change of
 -- coordinates of the output, through d truncated embeddings
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree ell of the immersion,
 --         the degree d of the truncation.
 
 -- output: a set of DAE to be solved to obtain the injection,
 --         the change of coordinates in implicit form.

 -- compute the set of all the embeddings of the system
 ss := allEmbedtr(R,f,h,N,d);
 
 -- compute the observability form of order ell
 vv := obsForm(ell);
 
 -- variables and coefficient rings
 coeffR := coefficientRing R;
 xx := gens R;
 n := length(xx);
 mm := numRows ss#0;
 
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 xvars := new List from xx_(0)..xx_(n-1);
 lx := lz + length xvars;
 y0vars := new List from y_0..y_0;
 ly0 := lx + length y0vars;
 avars := new List from a_0..a_(mm-1);
 la := ly0 + length avars;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := la + length kvars;
 tvars := new List from t_0..t_ell;
 lt := lk + length tvars;
 yvars := new List from y_1..y_ell;
 ly := lt + length yvars;
 
 AVars := zvars | xvars | y0vars | avars | kvars | tvars | yvars;
 
 S := QQ[AVars, MonomialOrder => Lex];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 xvars = new List from (nVars_(0,lz+1))..(nVars_(0,lx));
 -- print xvars;
 y0v := nVars_(0,lx+1);
 -- print y0v;
 avars = new List from (nVars_(0,ly0+1))..(nVars_(0,la));
 -- print avars;
 kvars = new List from (nVars_(0,la+1))..(nVars_(0,lk));
 -- print kvars;
 tvars = new List from (nVars_(0,lk+1))..(nVars_(0,lt));
 -- print tvars;
 yvars = new List from (nVars_(0,lt+1))..(nVars_(0,ly));
 -- print yvars;
 
 -- construct the generic embedding of the nonlinear system
 pp := 0;
 for ii from 0 to mm - 1 do (
  pp = pp + avars_ii*substitute((ss#1)_(ii,0),S);
 );
 qq := substitute((vv#0)_(1,0),S);
 
  -- minimum between N and ell
 Nellmin := min({N,ell});
 
 -- construction of the observability map
 obId1 := submatrix(substitute(ss#2,S),new List from 0..(Nellmin-1),{0});
 obId2 := submatrix(substitute(vv#1,S),new List from 0..(Nellmin-1),{0});
 
 -- find the set of equalities that has to be solved
 ylist := new List from yvars;
 (mons,coeffs) := coefficients(pp - qq, Variables => ylist);
 
 -- compute a Groebner basis of the equalities
 idcoeff := ideal(coeffs) + ideal(y0v-tvars_0); 
 G := transpose gens gb (idcoeff);
 
 -- return the Groebner basis and the equalities
 (G,obId1-obId2)
)

immObsNI = (R,f,h,N,ell) -> (
 -- compute the immersion of a nonlinear system  of the form
 -- dot{x} = f(x), y = h(x)
 -- into a linear one up to an output injection without change of
 -- coordinates of the output
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree ell of the immersion.
 
 -- output: the output injection,
 --         the change of coordinates from z to x,
 --         the change of coordinates from x to z.

  -- compute the set of all the embeddings of the system
 ss := allEmbed(R,f,h,N);
 
 -- compute the observability form of order ell without  
 -- change of coordinates in the output
 vv := obsFormNI(ell);
 
 -- variables and coefficient rings
 coeffR := coefficientRing R;
 xx := gens R;
 n := length(xx);
 mm := numRows ss#0;
 
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 xvars := new List from xx_(0)..xx_(n-1);
 lx := lz + length xvars;
 avars := new List from a_0..a_(mm-1);
 la := lx + length avars;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := la + length kvars;
 yvars := new List from y_0..y_ell;
 ly := lk + length yvars;
 
 AVars := zvars | xvars | avars | kvars |  yvars;
 
 S := QQ[AVars, MonomialOrder => Lex];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 xvars = new List from (nVars_(0,lz+1))..(nVars_(0,lx));
 -- print xvars;
 avars = new List from (nVars_(0,lx+1))..(nVars_(0,la));
 -- print avars;
 kvars = new List from (nVars_(0,la+1))..(nVars_(0,lk));
 -- print kvars;
 y0v := nVars_(0,lk+1);
 -- print y0v;
 yvars = new List from (nVars_(0,lk+2))..(nVars_(0,ly));
 -- print yvars;
 
 -- construct the generic embedding of the nonlinear system
 pp := 0;
 for ii from 0 to mm - 1 do (
  pp = pp + avars_ii*substitute((ss#0)_(ii,0),S);
 );
 qq := substitute((vv#0)_(0,0),S);
 
  -- minimum between N and ell
 Nellmin := min({N,ell});
 
 -- construction of the observability map
 obId1 := submatrix(substitute(ss#1,S),new List from 0..(Nellmin-1),{0});
 obId2 := submatrix(substitute(vv#1,S),new List from 0..(Nellmin-1),{0});
 
 -- find the set of equalities that has to be solved
 ylist := new List from yvars;
 (mons,coeffs) := coefficients(pp - qq, Variables => ylist);
 
 -- compute a Groebner basis of the equalities
 idcoeff := ideal(coeffs);
 -- print coeffs;
 G := transpose gens gb (idcoeff);
 
 -- print G;
 
 -- if aa = 0, then there does not exist any output injection
 flg := 0;
 for ii from 0 to mm-1 do (
  if avars_ii%ideal(G) != 0 then (
   flg = 1;
  );
 );
 if flg == 0 then (
  error "no output injection found";
 );
 
 pppG := G;
 G = transpose gens gb eliminate(ideal pppG, avars);
 -- print G;
 while numRows G < ell do (
  -- find a solution in A
  Ga := transpose mingens gb eliminate(ideal pppG, kvars|yvars|{y0v});
  -- print numRows G;
  Ra := coeffR[avars];
  ideA := substitute(ideal Ga,Ra);
  diea := dim ideA;
  -- print diea;
  ccdim := 0;
  for ii from 0 to mm - 1 do (
   if ccdim >=  diea then (
    break;
   );
   ddd := substitute(avars_ii,Ra)%ideA;
   expd := exponents leadTerm ddd;
   totDeg := 0;
   if length expd != 0 then (
    expd = expd#0;
    for kk from 0 to length expd - 1 do (
     totDeg = totDeg + expd#kk;
    );
   );
   if ddd != 0 and totDeg != 0 then (
    pppG = transpose gens gb (ideal pppG + ideal(avars#ii));
    G = transpose gens gb eliminate(ideal pppG,avars);
    break;
   );
  );
 );
 -- print G;
 
 -- solve the DAEs in G by integrating symbolically the polynomials in k
 lg := numRows G;
 kappa := new MutableList from 0..(n-1);
 kappaOut := new MutableList from 0..(n-1);
 indx := n-1;
 for ii from 0 to lg - 1 do (
  -- print kvars_(indx*ell);
  lt := leadTerm(G_(ii,0));
  if leadMonomial(lt) == kvars_(indx*ell) then (
   lc := leadCoefficient(G_(ii,0));
   kappa#(indx) = (lt - G_(ii,0))/lc;
   kappaOut#(indx) = kvars_(indx*ell)-(lt - G_(ii,0))/lc;
   indx = indx - 1;
  );
  if leadMonomial(lt) == kvars_(indx*ell+1) then (
   llc := leadCoefficient(G_(ii,0));
   tePol :=  y0v*(lt - G_(ii,0))/llc;
   mexp := 0;
   if tePol != 0 then (
    mexp = max new List from (exponents leadMonomial tePol)_(0);
   );
   parPol := 0;
   for kk from 1 to mexp do (
    coePol := coefficient(y0v^kk,tePol);
    parPol = parPol+coePol*1/kk*y0v^kk;
   );
   kappa#(indx) = parPol;
   kappaOut#(indx) = kvars_(indx*ell)-parPol;
   indx = indx - 1;
  );
  if indx == -1 then break;
 );
 kappa = new List from kappa;
 -- print kappa;
 kappa = transpose matrix{kappa};
 kappaOut = new List from kappaOut;
 kappaOut = transpose matrix{kappaOut};
 kappasubs := new MutableList;
 cont := 0;
 for ii from 0 to ell - 1 do (
  parpol := kappa_(ii,0);
  for jj from 0 to ell-1 do (
   kappasubs#cont = kvars_(ii*ell + jj) - parpol;
   parpol = diff(y0v,substitute(parpol,S));
   cont = cont + 1;
  );
 );
 kappasubs = new List from kappasubs;
 
 -- verify that the obtained solution solves also the other DAEs
 testIde := ideal(G) + ideal(kappasubs);
 -- print transpose gens testIde;
 GG := transpose gens gb testIde;
 if GG_(0,0) == 1 then (
  error "no output injection found";
 );
 
 -- compute the change of coordinates by substituting the obtained values
 chIde := ideal(obId1-obId2) + ideal(kappasubs) + ideal(y0v-substitute(h,S));
 
 klist := new List from kvars;
 ylist = new List from yvars;

 
 -- change of coordinate from x to z
 gbCh := transpose gens gb eliminate(chIde,klist|ylist|{y0v});
 -- print gbCh;
 ngbCH := new MutableList;
 for ii from 0 to numRows gbCh - 1 do (
  ngbCH#ii = gbCh_(numRows gbCh - 1 - ii,0);
 );
 ngbCH = new List from ngbCH;
 ngbCH = transpose matrix{ngbCH};
 
 -- change of coordinate from z to x
 nnVars := xvars | zvars | avars | kvars | {y0v} | yvars;
 
 S2 := coeffR[nnVars, MonomialOrder => Lex];
 gbCh2 := transpose gens gb substitute(ideal(gbCh),S2);
 ngbCh2 := new MutableList;
 for ii from 0 to numRows gbCh2 - 1 do (
  ngbCh2#ii = gbCh2_(numRows gbCh2 - 1 - ii,0);
 );
 ngbCh2 = new List from ngbCh2;
 ngbCh2 = transpose matrix{ngbCh2};
 
 -- return as output the k's and the direct/inverse change of coordinates
 (kappaOut, ngbCH, ngbCh2)
)

immObstrNI = (R,f,h,N,ell,d) -> (
 -- compute the immersion of a nonlinear system  of the form
 -- dot{x} = f(x), y = h(x)
 -- into a linear one up to an output injection without change of
 -- coordinates of the output and with embeddings truncation
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree ell of the immersion,
 --         the degree d of the truncation.
 
 -- output: the output injection,
 --         the change of coordinates from z to x,
 --         the change of coordinates from x to z.

  -- compute the set of all the d truncated embeddings of the system
 ss := allEmbedtr(R,f,h,N,d);
 
 -- compute the observability form of order ell without  
 -- change of coordinates in the output
 vv := obsFormNI(ell);
 
 -- variables and coefficient rings
 coeffR := coefficientRing R;
 xx := gens R;
 n := length(xx);
 mm := numRows ss#0;
 
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 xvars := new List from xx_(0)..xx_(n-1);
 lx := lz + length xvars;
 avars := new List from a_0..a_(mm-1);
 la := lx + length avars;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := la + length kvars;
 yvars := new List from y_0..y_ell;
 ly := lk + length yvars;
 
 AVars := zvars | xvars | avars | kvars |  yvars;
 
 S := QQ[AVars, MonomialOrder => Lex];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 xvars = new List from (nVars_(0,lz+1))..(nVars_(0,lx));
 -- print xvars;
 avars = new List from (nVars_(0,lx+1))..(nVars_(0,la));
 -- print avars;
 kvars = new List from (nVars_(0,la+1))..(nVars_(0,lk));
 -- print kvars;
 y0v := nVars_(0,lk+1);
 -- print y0v;
 yvars = new List from (nVars_(0,lk+2))..(nVars_(0,ly));
 -- print yvars;
 
 -- construct the generic embedding of the nonlinear system
 pp := 0;
 for ii from 0 to mm - 1 do (
  pp = pp + avars_ii*substitute((ss#1)_(ii,0),S);
 );
 qq := substitute((vv#0)_(0,0),S);
 
 -- construction of the observability map
 pobId1 := substitute(ss#2,S);
 obId1 := submatrix(pobId1,new List from 0..(n-1),{0});
 pobId2 := substitute(vv#1,S);
 obId2 := submatrix(pobId2,new List from 0..(n-1),{0});
 
 -- find the set of equalities that has to be solved
 ylist := new List from yvars;
 (mons,coeffs) := coefficients(pp - qq, Variables => ylist);
 
 -- compute a Groebner basis of the equalities
 idcoeff := ideal(coeffs);
 G := transpose gens gb (idcoeff);
 -- print G;
 
 -- if aa = 0, then there does not exist any output injection
 flg := 0;
 for ii from 0 to mm-1 do (
  if avars_ii%ideal(G) != 0 then (
   flg = 1;
  );
 );
 if flg == 0 then (
  error "no output injection found";
 );
 
 pppG := G;
 G = transpose gens gb eliminate(ideal pppG, avars);
 -- print G;
 while numRows G < ell do (
  -- find a solution in A
  Ga := transpose mingens gb eliminate(ideal pppG, kvars|yvars|{y0v});
  -- print numRows G;
  Ra := coeffR[avars];
  ideA := substitute(ideal Ga,Ra);
  diea := dim ideA;
  -- print diea;
  ccdim := 0;
  for ii from 0 to mm - 1 do (
   if ccdim >=  diea then (
    break;
   );
   ddd := substitute(avars_ii,Ra)%ideA;
   expd := exponents leadTerm ddd;
   totDeg := 0;
   if length expd != 0 then (
    expd = expd#0;
    for kk from 0 to length expd - 1 do (
     totDeg = totDeg + expd#kk;
    );
   );
   if ddd != 0 and totDeg != 0 then (
    pppG = transpose gens gb (ideal pppG + ideal(avars#ii));
    G = transpose gens gb eliminate(ideal pppG,avars);
    break;
   );
  );
 );
 -- print G;
 
 -- solve the DAEs in G by integrating symbolically the polynomials in k
 lg := numRows G;
 kappa := new MutableList from 0..(n-1);
 kappaOut := new MutableList from 0..(n-1);
 indx := n-1;
 for ii from 0 to lg - 1 do (
  -- print kvars_(indx*ell);
  lt := leadTerm(G_(ii,0));
  if leadMonomial(lt) == kvars_(indx*ell) then (
   lc := leadCoefficient(G_(ii,0));
   kappa#(indx) = (lt - G_(ii,0))/lc;
   kappaOut#(indx) = kvars_(indx*ell)-(lt - G_(ii,0))/lc;
   indx = indx - 1;
  );
  if leadMonomial(lt) == kvars_(indx*ell+1) then (
   llc := leadCoefficient(G_(ii,0));
   tePol :=  y0v*(lt - G_(ii,0))/llc;
   mexp := 0;
   if tePol != 0 then (
    mexp = max new List from (exponents leadMonomial tePol)_(0);
   );
   parPol := 0;
   for kk from 1 to mexp do (
    coePol := coefficient(y0v^kk,tePol);
    parPol = parPol+coePol*1/kk*y0v^kk;
   );
   kappa#(indx) = parPol;
   kappaOut#(indx) = kvars_(indx*ell)-parPol;
   indx = indx - 1;
  );
  if indx == -1 then break;
 );
 kappa = new List from kappa;
 -- print kappa;
 kappa = transpose matrix{kappa};
 kappaOut = new List from kappaOut;
 kappaOut = transpose matrix{kappaOut};
 kappasubs := new MutableList;
 cont := 0;
 for ii from 0 to ell - 1 do (
  parpol := kappa_(ii,0);
  for jj from 0 to ell-1 do (
   kappasubs#cont = kvars_(ii*ell + jj) - parpol;
   parpol = diff(y0v,substitute(parpol,S));
   cont = cont + 1;
  );
 );
 kappasubs = new List from kappasubs;
 
 -- verify that the obtained solution solves also the other DAEs
 testIde := ideal(G) + ideal(kappasubs);
 -- print transpose gens testIde;
 GG := transpose gens gb testIde;
 if GG_(0,0) == 1 then (
  error "no output injection found";
 );
 
 -- compute the change of coordinates by substituting the obtained values
 chIde := ideal(obId1-obId2) + ideal(kappasubs) + ideal(y0v-substitute(h,S));
 
 klist := new List from kvars;
 ylist = new List from yvars;

 
 -- change of coordinate from x to z
 gbCh := transpose gens gb eliminate(chIde,klist|ylist|{y0v});
 -- print gbCh;
 ngbCH := new MutableList;
 for ii from 0 to numRows gbCh - 1 do (
  ngbCH#ii = gbCh_(numRows gbCh - 1 - ii,0);
 );
 ngbCH = new List from ngbCH;
 ngbCH = transpose matrix{ngbCH};
 
 -- change of coordinate from z to x
 nnVars := xvars | zvars | avars | kvars | {y0v} | yvars;
 
 S2 := coeffR[nnVars, MonomialOrder => Lex];
 gbCh2 := transpose gens gb substitute(ideal(gbCh),S2);
 ngbCh2 := new MutableList;
 for ii from 0 to numRows gbCh2 - 1 do (
  ngbCh2#ii = gbCh2_(numRows gbCh2 - 1 - ii,0);
 );
 ngbCh2 = new List from ngbCh2;
 ngbCh2 = transpose matrix{ngbCh2};
 
 -- return as output the k's and the direct/inverse change of coordinates
 (kappaOut, ngbCH, ngbCh2)
)

approxSolODE = (eq,deg,ODEg) -> (
 -- solve a ODE by approximating the functions through polynomials
 
  -- inputs: the eqation eq 
 --          the degree deg of the approximation
 --          the degree ODEg of the ODE.
 
 -- output: the coefficients of the solution.

 -- coefficient ring
 
 pS := QQ[b_0..b_(ODEg+deg),t_0..t_ODEg, z_1];
 nVars := vars pS;
 
 blist := new List from (nVars_(0,0))..(nVars_(0,ODEg+deg));
 -- print blist;
 tvars := new List from (nVars_(0,ODEg+deg+1))..(nVars_(0,2*ODEg+deg+1));
 -- print tvars;
 zvars := nVars_(0,2*ODEg+deg+2);
 -- print zvars;
 
 S := frac(QQ[blist])[tvars|{zvars}];
 
 -- base polynomial
 bpol := substitute(0,S);
 for ii from 0 to ODEg + deg do (
  bpol = bpol + substitute(blist_ii,S)*substitute(zvars^ii,S);
 );
 
 -- derivatives of the polynomial
 derPol := new MutableList;
 derPol#0 = substitute(bpol,S);
 for ii from 1 to ODEg do (
  derPol#ii = diff(substitute(zvars,S),derPol#(ii-1));
 );
 derPol = new List from derPol;
 
 -- print derPol;
 
 -- substitute the derivatives into the expression
 neqq := substitute(eq,S);
 for ii from 0 to ODEg do (
  neqq = substitute(neqq, substitute(tvars_ii,S) => derPol#ii);
 );
 
 -- new polynomial ring
 S2 := QQ[blist, MonomialOrder => Lex];
 
 -- extract the equalities
 eqList := new MutableList;
 for ii from 0 to deg do (
  eqList#ii = substitute(coefficient(substitute(zvars^ii,S), neqq),S2);
 );
 eqList = new List from eqList;

 -- print transpose matrix{eqList};
 
 -- define the ideal from the equalities
 ideEq := ideal(eqList);
 elList := new List from substitute(blist_(deg+1),S2)..substitute(blist_(ODEg+deg),S2);
 
 -- compute a Groebner basis of the ideal
 G := transpose mingens gb eliminate(ideEq,elList);
 
 -- return the gb and the polynomial
 (transpose matrix{eqList}, G)
)

compMatr = (R,I,f) -> (
 -- this function computes the companion matrix, associated to the 
 -- function f, of the ideal I over the ring R. The ideal I needs to be zero dimensional
 -- over the ring R, otherwise the function returns an error.
 
 -- inputs: the ring R where the ideal is defied,
 --         the ideal I,
 --         the function f,
 
 -- output: the companion matrix associated to associated to the 
 --         function f, of the ideal I over the ring R.
 
 -- check that the ideal I is zero dimensional.
 if dim I != 0 then 
  error "the ideal is not zero dimensional";
 
 -- compute the quotient ring R/I and a monomial basis of this quotient ring.
 quotRing := R/I;
 B := basis(quotRing);
 
 -- m denotes the number of elements in the basis (i.e., the number of different complex
 -- point in the affine variety V(I)).
 m := numgens source B;
 
 -- compute the linear map M: R/I -> R/I, (f*g mod I) = (M*g mod I).
 M := new MutableMatrix from id_(quotRing^m);
 for jj from 0 to m-1 do (
  colVal := f*B_(0,jj);
  for ii from 0 to m-1 do (
   v := coefficient(B_(0,ii),colVal);
   vv := promote(v,quotRing);
   M_(ii,jj) = vv;
  );
 );
 out := new Matrix from M;
 
 -- the function returns the linear map M.
 out
);

solveSystem = (R,I) -> (
 -- this function computes the coordinates of the points in the affine variety V(I).
 -- the ideal I needs to be zero dimensional, otherwise the function returns an error.
 
 -- inputs: the ring R where the ideal is defined,
 --         the ideal I.
 
 -- output: a matrix expressing the complex coordinates of the points in V(I).
 --         The matrix is organized as follows:
 --          1) each row is a point in V(I);
 --          2) the columns are arranged according to the order of the 
 --             variables in the ring R.
 
 -- check if the ideal is zero dimensional.
 if dim I != 0 then 
  error "the ideal is not zero dimensional";
 
 -- define the variables vector.
 var := gens R;
 
 -- compute the quotient ring R/I and a monomial basis.
 quotRing := R/I;
 B := basis(quotRing);
 
 -- m denotes the number of elements in the basis (i.e., the number of different complex
 -- point in the affine variety V(I)).
 m := numgens source B;
 
 -- define the coefficient ring. 
 coeffRing := coefficientRing(R);
 
 -- n denotes the number of variables to be considered
 n := length var;
 
 -- solMat denotes the list of the companion matrices associated to the
 -- ring R variables of the ideal I.
 solMat := {};
 
 -- if there is a single variable return the eigenvalues of the companion matrix
 -- associated to such a variable,
 if n == 1 then (
  solMat = substitute(compMatr(R,I,var_(ii-1)),coeffRing);
  eigenvalues(solMat)
 ) 
 
 -- otherwise compute the eigenvectors of the first companion matrix and use them
 -- to find all the coordinates of the points in V(I) (the method used here to compute 
 -- such points is based on the Stickelberger’s Theorem).
 else (
 
  -- each row of the matrix solutions is a point in the affine variety V(I),
  -- the columns are arranged according to the order of the variables in the ring R.
  solutions := new MutableMatrix from random(CC^m,CC^n);
  
  -- computation ot the companion matrices of the ideal I.
  for kk from 1 to n do (
   solMat = append(solMat,substitute(compMatr(R,I,var_(kk-1)),coeffRing));
  );
  
  -- computation of the eigenvectors of the companion matrices (they have 
  -- the same set of eigenvectors).
  eigVec := (eigenvectors(solMat_(0)))_(1);
  
  -- computation of the associated eigenvalues, which constitute a point in V(I).
  flag := 0;
  for ii from 0 to m-1 do (
   vecs := eigVec_{ii};
   for jj from 0 to n-1 do (
    MMM := solMat_(jj);
    index := -1;
    parvec := MMM*vecs;
    for ll from 0 to numrows eigVec - 1 do (
     if vecs_(ll,0) != 0+0*ii then (
      index = ll;
      break;
     );
    );
    pareig := (parvec_(index,0))/(vecs_(index,0));
    for ll from 0 to numrows eigVec - 1 do(
     if abs(pareig*vecs_(ll,0) - parvec_(ll,0)) > 10^(-9) then (
      flag = 1;
      print("eigenvectors not matching");
      break;
     );
     if flag == 0 then (
      solutions_(ii,jj) = pareig;
     );
    );
   );
  
   if flag == 1 then (
    break;
   );
  );
  
  -- the function returns the vector of the solutions
  out := 0;
  if flag == 0 then (
   out = new Matrix from solutions;
  ) else (
   error "not able to compute a solution";
  );
  out
 )
);

rationalize = (num,prec) -> (
 -- compute the nearest rational with fixed precision
 
 -- inputs: a real number num,
 --         the precision prec.
 
 -- output: a rational approximation of num
 
 nnum := round(num*10^prec);
 out := nnum / 10^prec;
 out
)

immObstrNum = (R,f,h,N,ell,d,deg) -> (
 -- compute numerically the immersion of a nonlinear system  of the form
 -- dot{x} = f(x), y = h(x)
 -- into a linear one up to an output injection with change of
 -- coordinates of the output and with embeddings truncation
 
 -- inputs: the ring R where the ideal is defied,
 --         the vector field f,
 --         the function h,
 --         the order N of the observability matrix,
 --         the degree ell of the immersion,
 --         the degree d of the truncation,
 --         the degree deg of the approximation.
 
 -- output: the change of coordinates for the output,
 --         the output injection,
 --         the change of coordinates from z to x,
 --         the change of coordinates from x to z.

  -- compute the set of all the embeddings of the system
 ss := allEmbedtr(R,f,h,N,d);
 
 -- variables and coefficient rings
 coeffR := coefficientRing R;
 xx := gens R;
 n := length(xx);
 mm := numRows ss#0;
 
 zvars := new List from z_1..z_ell;
 lz := length zvars - 1;
 xvars := new List from xx_(0)..xx_(n-1);
 lx := lz + length xvars;
 avars := new List from a_0..a_(mm-1);
 la := lx + length avars;
 kvars := new List from k_(1,0)..k_(ell,ell-1);
 lk := la + length kvars;
 yvars := new List from y_0..y_ell;
 ly := lk + length yvars;
 tvars := new List from t_0..t_ell;
 lt := ly + length tvars;
 
 AVars := zvars | xvars | avars | kvars | yvars | tvars;
 
 S := QQ[AVars, MonomialOrder => Lex];
 nVars := vars S;
 -- print nVars;
 
 zvars = new List from (nVars_(0,0))..(nVars_(0,lz));
 -- print zvars;
 xvars = new List from (nVars_(0,lz+1))..(nVars_(0,lx));
 -- print xvars;
 avars = new List from (nVars_(0,lx+1))..(nVars_(0,la));
 -- print avars;
 kvars = new List from (nVars_(0,la+1))..(nVars_(0,lk));
 -- print kvars;
 y0v := nVars_(0,lk+1);
 -- print y0v;
 yvars = new List from (nVars_(0,lk+2))..(nVars_(0,ly));
 -- print yvars;
 tvars = new List from (nVars_(0,ly+1))..(nVars_(0,lt));
 -- print tvars;
 
 -- compute the solution through truncation
 GO := immObstr(R,f,h,N,ell,d);
 -- print GO;
 soleq := new MutableList;
 for ii from 0 to numRows GO#0 - 1 do (
  soleq#ii = substitute((GO#0)_(ii,0),S);
 );
 soleq = new List from soleq;
  
 -- keep just the terms that depend on t
 GG := transpose gens gb eliminate(ideal soleq,avars|kvars|{y0v});
 -- print GG;
 polTheta := substitute(0,S);
 z1v := zvars_(0);
  
 -- if GG is not empty
 if numRows GG != 0 then (
  -- define the new coefficient ring
  S2 := QQ[b_0..b_deg];
  s2Vars := vars S2;
 
  -- obtain equalities for the coefficient
  ttr := (approxSolODE(GG_(0,0),deg,ell))#1;
  -- print ttr;
  pcont := 0;
  eqCoeff := new MutableList;
  for jj from 0 to numRows ttr - 1 do (
   eqCoeff#pcont = substitute(ttr_(jj,0),S2);
   pcont = pcont + 1;
  );
  for ii from 1 to numRows GG - 1 do (
   tempList := (approxSolODE(GG_(ii,0),deg,ell))#1;
   -- print tempList;
   for jj from 0 to numRows tempList - 1 do (
    eqCoeff#pcont = substitute(tempList_(jj,0),S2);
    pcont = pcont + 1;
   );
  );
  eqCoeff = new List from eqCoeff;
  eqCoeff = transpose matrix{eqCoeff};
  
  -- define the ideal of the equalities to be found
  Is2 := ideal(0);
  for ii from 0 to numRows eqCoeff - 1 do (
   Is2 = Is2 + ideal(eqCoeff_(ii,0));
  );
  
  -- print transpose gens Is2;
  
  -- compute the dimension of the ideal
  dimS2 := dim Is2;
  
  -- print dimS2;
  
  -- if the dimension is -1 there is no solution
  if dimS2 == -1 then (
   error "there is no solution";
  );
  
  -- fix some variables to have a zero dimensional ideal
  for ii from 0 to dimS2 - 1 do (
   Is2 = Is2 + ideal(s2Vars_(0,ii)+substitute(1+random(ZZ),S2));
  );
  
  -- print transpose gens Is2;
  
  -- solve the system of equalities
  solB := solveSystem(S2,Is2);
  -- print solB;
  for ii from 0 to numColumns solB - 1 do (
   polTheta = polTheta + rationalize(solB_(0,ii),6)*substitute(z1v^ii,S);
  );
 ) else (
  polTheta = substitute(z1v,S);
 );
 
 -- print polTheta;
 
 -- substitute the obtained solution
 nIdSol := ideal(soleq);
 for ii from 0 to ell do (
  nIdSol = nIdSol + ideal(tvars_ii - diff(z1v^ii,polTheta));
 );
 
 -- verify the solution
 vvG := transpose gens gb nIdSol;
 flg := 0;
 for ii from 0 to mm-1 do (
  if avars_ii%ideal(vvG) != 0 then (
   flg = 1;
  );
 );
 if flg == 0 then (
  error "no output injection found";
 );
 
 -- find a solution in k
 -- print transpose gens nIdSol;
 pG := transpose gens gb eliminate(nIdSol, tvars|{y0v}|avars);
 -- print G;
 G := new MutableMatrix from pG;
 for ii from 0 to numRows pG - 1 do (
  G_(ii,0) = substitute(pG_(ii,0), z1v => y0v);
 );
 G = new Matrix from G;
 G = transpose gens gb ideal(G);
 
 -- if aa = 0, then there does not exist any output injection
 flg = 0;
 for ii from 0 to mm-1 do (
  if avars_ii%ideal(G) != 0 then (
   flg = 1;
  );
 );
 if flg == 0 then (
  error "no output injection found";
 );
 
 pppG := G;
 G = transpose gens gb eliminate(ideal pppG, avars);
 -- print G;
 while numRows G < ell do (
  -- find a solution in A
  Ga := transpose mingens gb eliminate(ideal pppG, kvars|yvars|{y0v});
  -- print numRows G;
  Ra := coeffR[avars];
  ideA := substitute(ideal Ga,Ra);
  diea := dim ideA;
  -- print diea;
  ccdim := 0;
  for ii from 0 to mm - 1 do (
   if ccdim >=  diea then (
    break;
   );
   ddd := substitute(avars_ii,Ra)%ideA;
   expd := exponents leadTerm ddd;
   totDeg := 0;
   if length expd != 0 then (
    expd = expd#0;
    for kk from 0 to length expd - 1 do (
     totDeg = totDeg + expd#kk;
    );
   );
   if ddd != 0 and totDeg != 0 then (
    pppG = transpose gens gb (ideal pppG + ideal(avars#ii));
    G = transpose gens gb eliminate(ideal pppG,avars);
    break;
   );
  );
 );
 -- print G;
 
 -- solve the DAEs in G by integrating symbolically the polynomials in k
 lg := numRows G;
 kappa := new MutableList from 0..(n-1);
 kappaOut := new MutableList from 0..(n-1);
 indx := n-1;
 for ii from 0 to lg - 1 do (
  -- print kvars_(indx*ell);
  lt := leadTerm(G_(ii,0));
  if leadMonomial(lt) == kvars_(indx*ell) then (
   lc := leadCoefficient(G_(ii,0));
   kappa#(indx) = (lt - G_(ii,0))/lc;
   kappaOut#(indx) = kvars_(indx*ell)-(lt - G_(ii,0))/lc;
   indx = indx - 1;
  );
  if leadMonomial(lt) == kvars_(indx*ell+1) then (
   llc := leadCoefficient(G_(ii,0));
   tePol :=  y0v*(lt - G_(ii,0))/llc;
   mexp := 0;
   if tePol != 0 then (
    mexp = max new List from (exponents leadMonomial tePol)_(0);
   );
   parPol := 0;
   for kk from 1 to mexp do (
    coePol := coefficient(y0v^kk,tePol);
    parPol = parPol+coePol*1/kk*y0v^kk;
   );
   kappa#(indx) = parPol;
   kappaOut#(indx) = kvars_(indx*ell)-parPol;
   indx = indx - 1;
  );
  if indx == -1 then break;
 );
 kappa = new List from kappa;
 -- print kappa;
 kappa = transpose matrix{kappa};
 kappaOut = new List from kappaOut;
 kappaOut = transpose matrix{kappaOut};
 kappasubs := new MutableList;
 kappasubs2 := new MutableList;
 cont := 0;
 for ii from 0 to ell - 1 do (
  parpol := kappa_(ii,0);
  for jj from 0 to ell - 1 do (
   kappasubs#cont = kvars_(ii*ell + jj) - parpol;
   kappasubs2#cont = kvars_(ii*ell + jj) - substitute(parpol, y0v => z1v);
   parpol = diff(y0v,substitute(parpol,S));
   cont = cont + 1;
  );
 );
 kappasubs = new List from kappasubs;
 kappasubs2 = new List from kappasubs2;
 
 -- print G;
 -- print kappa;
 
 -- verify that the obtained solution solves also the other DAEs
 testIde := ideal(G) + ideal(kappasubs);
 -- print transpose gens testIde;
 GGG := transpose gens gb testIde;
 if GGG_(0,0) == 1 then (
  error "no output injection found";
 );
 
 polTheta = substitute(polTheta, y0v => z1v);
 kappaOut = substitute(kappaOut, y0v => z1v);
 -- print kappasubs2;
 
 -- compute the change of coordinates by substituting the obtained values
 chbas := submatrix(GO#1,new List from 0..(n-1),{0});
 -- print chbas;
 chIde := substitute(ideal(chbas),S) + ideal(kappasubs2);
 for ii from 0 to ell do (
  chIde = chIde + ideal(tvars_ii - diff(z1v^ii,polTheta));
 );
 
 klist := new List from kvars;
 ylist := new List from yvars;

 -- change of coordinate from x to z
 gbCh := transpose gens gb eliminate(chIde,klist|ylist|{y0v}|tvars);
 -- print gbCh;
 ngbCH := new MutableList;
 for ii from 0 to numRows gbCh - 1 do (
  ngbCH#ii = gbCh_(numRows gbCh - 1 - ii,0);
 );
 ngbCH = new List from ngbCH;
 ngbCH = transpose matrix{ngbCH};
 
 -- change of coordinate from z to x
 nnVars :=  xvars | zvars | avars | kvars | {y0v} | yvars;
 
 S4 := coeffR[nnVars, MonomialOrder => Lex];
 gbCh2 := transpose gens gb substitute(ideal(gbCh),S4);
 ngbCh2 := new MutableList;
 for ii from 0 to numRows gbCh2 - 1 do (
  ngbCh2#ii = gbCh2_(numRows gbCh2 - 1 - ii,0);
 );
 ngbCh2 = new List from ngbCh2;
 ngbCh2 = transpose matrix{ngbCh2};
 
 S5 := coeffR[kvars | zvars,MonomialOrder => Lex];
 kappaOut = substitute(kappaOut,S5);
 
 -- return the change of coordinates for the output and the immersion
 (polTheta,kappaOut,ngbCH,ngbCh2)
)

-- End of source code ---

beginDocumentation()

document { 
 Key => {OutputInjection},
 Headline => "a package for computing an output injection",
 EM "Output Injection", " is a package for polynomial dynamical systems. 
 It is used to determine, if any, the immersion of a polynomial system into 
 a linear one, up to an output injection."
}

document {
 Key => {allEmbed},
 Headline => "Compute embeddings.",
 Consequences => {"Computation of all the embeddings of 
  order N of the nonlinear system dot{x} = f(x), y = h(x)."},
 Usage => "allEmbed(R,f,h,N)",
 Inputs => {
  "R" => { "the ring where the system is defied."},
  "f" => { "the vector field such that dot{x} = f(x)."},
  "h" => { "the output function such that y = h(x)."},
  "N" => { "the order of the embeddings."}
 },
 Outputs => {
  "G" => { "the Groebner basis of the ideal of the embeddings."},
  "I" => { "a basis of the observation ideal."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = allEmbed(R,f,h,2)"
 },
 SeeAlso => allEmbedtr
}

document {
 Key => {allEmbedtr},
 Headline => "Truncated embeddings.",
 Consequences => {"Computation of all the d-truncated embeddings of 
  order N of the nonlinear system dot{x} = f(x), y = h(x)."},
 Usage => "allEmbedtr(R,f,h,N,d)",
 Inputs => {
  "R" => { "the ring where the system is defied."},
  "f" => { "the vector field such that dot{x} = f(x)."},
  "h" => { "the output function such that y = h(x)."},
  "N" => { "the order of the embeddings."},
  "d" => { "the degree of the truncation."}
 },
 Outputs => {
  "G"  => { "the Groebner basis of the ideal of the embeddings."},
  "nG" => { "the set of generators of the d truncated embeddings."},
  "I"  => { "a basis of the observation ideal."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = allEmbedtr(R,f,h,2,1)"
 },
 SeeAlso => allEmbed
}

document {
 Key => {obsForm},
 Headline => "Observability form.",
 Consequences => {"Computation of the embedding of the generic system in linear up to an
  output feedback form, with output transformation."},
 Usage => "obsForm(ell)",
 Inputs => {
  "ell" => { "the degree of the system."}
 },
 Outputs => {
  "G"  => { "the Groebner basis of the ideal of the embeddings."},
  "I"  => { "a basis of the observation ideal."} 
 }, 
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "obf = obsForm(2)"
 },
 SeeAlso => {obsFormNI}
}

document {
 Key => {obsFormNI},
 Headline => "Observability form without transformation.",
 Consequences => {"Computation of the embedding of the generic system in linear up to an
  output feedback form, without output transformation."},
 Usage => "obsFormNI(ell)",
 Inputs => {
  "ell" => { "the degree of the system."}
 },
 Outputs => {
  "G"  => { "the Groebner basis of the ideal of the embeddings."},
  "I"  => { "a basis of the observation ideal."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "obf = obsFormNI(2)"
 },
 SeeAlso => {obsForm}
}

document {
 Key => {immObs},
 Headline => "Immersion into LIS form.",
 Consequences => {"compute the immersion of a nonlinear system  of the form
  dot{x} = f(x), y = h(x), into a linear one up to an output injection 
  with change of coordinates of the output."},
 Usage => "immObs(R,f,h,N,ell)",
 Inputs => {
  "R"   => { "the ring where the system is defied."},
  "f"   => { "the vector field such that dot{x} = f(x)."},
  "h"   => { "the output function such that y = h(x)."},
  "N"   => { "the order of the embeddings."},
  "ell" => { "the degree of the linear system."}
 },
 Outputs => {
  "G"    => { "a set of DAE to be solved to obtain the injection."},
  "obI"  => { "the change of coordinates in implicit form."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = immObs(R,f,h,2,2)"
 },
 SeeAlso => {immObstr,immObsNI,immObstrNI,immObstrNum}
}

document {
 Key => {immObstr},
 Headline => "Truncated immersion into LIS form.",
 Consequences => {"compute the immersion of a nonlinear system  of the form
  dot{x} = f(x), y = h(x), into a linear one up to an output injection 
  with change of coordinates of the output, through d truncated embeddings."},
 Usage => "immObstr(R,f,h,N,ell,d)",
 Inputs => {
  "R"   => { "the ring where the system is defied."},
  "f"   => { "the vector field such that dot{x} = f(x)."},
  "h"   => { "the output function such that y = h(x)."},
  "N"   => { "the order of the embeddings."},
  "ell" => { "the degree of the linear system."},
  "d"   => { "the degree of the truncation."}
 },
 Outputs => {
  "G"    => { "a set of DAE to be solved to obtain the injection."},
  "obI"  => { "the change of coordinates in implicit form."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = immObstr(R,f,h,2,2,1)"
 },
 SeeAlso => {immObs,immObsNI,immObstrNI,immObstrNum}
}

document {
 Key => {immObsNI},
 Headline => "Immersion into LIS form without transformation.",
 Consequences =>  {"compute the immersion of a nonlinear system  of the form
  dot{x} = f(x), y = h(x), into a linear one up to an output injection 
  without change of coordinates of the output."},
 Usage => "immObsNI(R,f,h,N,ell)",
 Inputs => {
  "R"   => { "the ring where the system is defied."},
  "f"   => { "the vector field such that dot{x} = f(x)."},
  "h"   => { "the output function such that y = h(x)."},
  "N"   => { "the order of the embeddings."},
  "ell" => { "the degree of the linear system."}
 },
 Outputs => {
  "kappa"  => { "the output injection."},
  "ngbCH"  => { "the change of coordinates from z to x."}, 
  "ngbCH2" => { "the change of coordinates from x to z."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3}}",
  "h = x_1",
  "GI = immObsNI(R,f,h,2,2)"
 },
 SeeAlso => {immObs,immObstr,immObstrNI,immObstrNum}
}

document {
 Key => {immObstrNI},
 Headline => "Truncated immersion into LIS form without transformation.",
 Consequences => {"compute the immersion of a nonlinear system  of the form
  dot{x} = f(x), y = h(x), into a linear one up to an output injection 
  without change of coordinates of the output and with embeddings truncation."},
 Usage => "immObsNI(R,f,h,N,ell,d)",
 Inputs => {
  "R"   => { "the ring where the system is defied."},
  "f"   => { "the vector field such that dot{x} = f(x)."},
  "h"   => { "the output function such that y = h(x)."},
  "N"   => { "the order of the embeddings."},
  "ell" => { "the degree of the linear system."},
  "d"   => { "the degree of the truncation."}
 },
 Outputs => {
  "kappa"  => { "the output injection."},
  "ngbCH"  => { "the change of coordinates from z to x."}, 
  "ngbCH2" => { "the change of coordinates from x to z."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = immObstrNI(R,f,h,2,2,1)"
 },
 SeeAlso => {immObs,immObstr,immObsNI,immObstrNum}
}

document {
 Key => {approxSolODE},
 Headline => "Solution to an ODE.",
 Consequences => { "solve an univariate ODE by approximating the solution through
  its Taylor expansion up to a finite order."},
 Usage => "approxSolODE (eq,deg,ODEg)",
 Inputs => {
  "eq"   => { "the ODE to be solved."},
  "deg"  => { "the degree of the Taylor expansion."},
  "ODEg" => { "the degree of the ODE."}
 },
 Outputs => {
  "eqList"  => { "the equations that have to be satisfied."},
  "G"       => { "the Groebner basis of the solution."}, 
  "theta"   => { "the polynomial expression of the solution."} 
 },
 EXAMPLE {
  "S = frac(QQ)[t_0..t_2]",
  "nvars = vars S",
  "ODE = nvars_(0,1)^2 - nvars_(0,0)*nvars_(0,2)",
  "approxSolODE(ODE,3,2)"
 },
 SeeAlso => {immObs,immObstr,immObstrNum}
}

document { 
 Key => {compMatr},
 Headline => "Companion matrix.",
 Consequences => { "Computation of the companion matrix"},
 Usage => "compMatr(R,I,f)",
 Inputs => {
  "R" => { "a ring, where the ideal I is defined"},
  "I" => { "a zero dimensional ideal."},
  "f" => { "a polynomial in R."} 
 },
 Outputs => {
  "M" => {"the companion matrix associated to the polynomial
	       f of the ideal I."}
 },
 EXAMPLE {
  "R = QQ[x_1..x_3]",
  "f = x_1^2+3*x_2-x_3",
  "I = ideal(x_1+x_2-x_3^2, x_1*x_2-x_2^2, x_3-x_2)",
  "M = compMatr(R,I,f)"
 },
 SeeAlso => solveSystem
}   
    
document { 
 Key => {solveSystem},
 Headline => "Solve a polynomial system.",
 Consequences => {"Computation of the solutions to a system of polynomial equalities"},
 Usage => "solveSystem(R,I)",
 Inputs => {
  "R" => { "a ring, where the ideal I is defined"},
  "I" => { "a zero dimensional ideal."}
 },
 Outputs => {
  "S" => {"the matrix with the points in the affine variety V(I).
	       The matrix is organized as follows:
            1) each row is a point in V(I);
            2) the columns are arranged according to the order of the 
                variables in the ring R."}
 },
 EXAMPLE {
  "R = QQ[x_1..x_3]",
  "I = ideal(x_1+x_2-x_3^2, x_1*x_2-x_2^2, x_3-x_2)",
  "M = solveSystem(R,I)"
 },
 SeeAlso => compMatr
} 

document {
 Key => {rationalize},
 Headline => "Rationalize a real number.",
 Consequences => {"Compute the rational number nearest to a given 
  real number with fixed precision."},
 Usage => "raionalize(num,prec)",
 Inputs => {
  "num"  => { "a real number."},
  "prec" => { "the precision of the approximation."}
 },
 Outputs => {
  "rat" => { "a rational approximation of the input."}
 },
 EXAMPLE {
  "rationalize(1.32,2)",
 },
 SeeAlso => {immObstrNum}
}

document {
 Key => {immObstrNum},
 Headline => "Numerical immersion into LIS form with transformation.",
 Consequences => { "compute numerically the immersion of a nonlinear system  of the form
  dot{x} = f(x), y = h(x) into a linear one up to an output injection with change of
  coordinates of the output and with embeddings truncation"},
 Usage => "immObstrNum(R,f,h,N,ell,d,deg)",
 Inputs => {
  "R"   => { "the ring where the system is defied."},
  "f"   => { "the vector field such that dot{x} = f(x)."},
  "h"   => { "the output function such that y = h(x)."},
  "N"   => { "the order of the embeddings."},
  "ell" => { "the degree of the linear system."},
  "d"   => { "the degree of the truncation."},
  "deg" => { "the degree of the approximation."}
 },
 Outputs => {
  "theta"  => { "the change of coordinates of the output."},
  "kappa"  => { "the output injection."},
  "ngbCH"  => { "the change of coordinates from z to x."}, 
  "ngbCH2" => { "the change of coordinates from x to z."} 
 },
 EXAMPLE {
  "R = frac(QQ)[x_1..x_2]",
  "f = matrix{{x_2+x_1^2},{-x_1+x_1^3-x_2^4-x_1*x_2}}",
  "h = x_1",
  "GI = immObstrNum(R,f,h,2,2,1,2)",
 },
 SeeAlso => {immObs,immObstr,immObsNI,immObstrNI,solveSystem,approxSolODE,rationalize}
}
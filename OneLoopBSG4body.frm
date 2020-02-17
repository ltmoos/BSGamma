Symbol d;
Dimension d;
Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a),g,gden;
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga2five,hf,eps(a),eta(s),sym,asym,epssign;
Indices mu,nu,rho,photind,gluind,mu1,...,mu100,dum1,...,dum10,five;
Symbol k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2    ,s12,s13,s14,s23,s24,s34,convfac1proj,mark1,...,mark50,asbar,ab,au,aubar,qk1,...,qk4,eps134k,eps234k,eps124k,eps123k,eps1234;
Vectors pp1,p1,...,p10,q1,...,q10,q,q14,q24,q34,q123,pu,pubar,ps,psbar,pb,pbbar,k1,...,k4;
Tensor O1,O,O1c,Obu,Osu,Obuc,Osuc,Ouu,Ouuc,Osb,Osbc;
Off Statistics;


* Diagrams from QGRAF
#include- all3vertxNEWvrtx.h;
#include- diagrams1l.h;


* Conjugation Routine
#include- conjugate.h;

* Routines for the Product of Eps*Eps, simplification of eta*eta and the
* Traces from FeynCalc
#include- ProdTwoEps_eps_eta.h;
#include- etasimp.h

* only need to include the following if internal trace routine is not used
* (external is (much) slower but consistent)
*#include- tracesNoG5.h;
*#include- trace12.h;
*#include- trace14.h;

* Kinematics relevant for the process:

#include- KinematicsBSG4Body.h;

*
* split 4-vertex in 2 2-vertices and give them dirac structure
* create ga() as prototype to be converted to g_
*

* resolve the 4-vertex into the
* pinguin structure (sbar-b)(ubar-u)

id  vrtx(sbar(asbar?,psbar?),u(au?,pu?),ubar(aubar?,pubar?),b(ab?,pb?)) = vrtx(sbar(asbar,psbar),b(ab,pb))*vrtx(ubar(aubar,pubar),u(au,pu));

id  vrtx(ubar(aubar?,pubar?),u(au?,pu?)) = ga(aubar,Ouu,au);
id  vrtx(sbar(asbar?,psbar?),b(ab?,pb?)) = ga(asbar,Osb,ab);

* give the propagator a second index needed for the routine below

id prop(f?(a1?,p1?))=prop2(f(a1,a1+1,p1));

*
* put spinors and propagators in ga-functions (-> contracting the indices)
* CHECK the sign vs. flow parts!!! (were consistent @ treelvl)
*
repeat;
id ga(?a1,O?,a2?)*prop2(s?(a3?,a2?,p1?))=ga(?a1,O,prop(s(p1)),a3);
id pol(photon(n1?,p1?))=p(li(n1),p1);
id pol(b?(n1?,p1?))*ga(n1?,?a2)=ga(b(p1),?a2);
id pol(b?(n1?,p1?))*ga(?a2,n1?)=ga(?a2,b(p1));
id ga(?a1,a2?)*prop2(u?(a2?,a3?,p1?))=ga(?a1,prop(u(p1)),a3);
id ga(a1?,?a2)*prop2(u?(a3?,a1?,p1?))=ga(a3,prop(u(p1)),?a2);

id ga(a1?,?a2)*prop2(u?(a1?,a3?,p1?))=ga(a3,prop(u(p1)),?a2); *(?SIGN?)

*photon vertices

id ga(?a1,a2?)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,p3?))=ga(?a1,li(photind),a3);
id ga(a1?,?a2)*vrtx(ubar?(a3?, p1?),u?(a1?,p2?),photon(a4?,p3?))=
ga(a3,li(photind),?a2);

id ga(a2?,?a1)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,p3?))=
ga(a3,li(photind),?a1); *(?SIGN?)
id ga(?a1,a2?)*vrtx(ubar?(a3?, p1?),u?(a2?,p2?),photon(a4?,p3?))=
ga(?a1,li(photind),a3); *(?SIGN?)

*gluon vertices

id ga(?a1,a2?)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),g(a4?,p3?))=ga(?a1,li(gluind),a3);
id ga(a1?,?a2)*vrtx(ubar?(a3?, p1?),u?(a1?,p2?),g(a4?,p3?))=
ga(a3,li(gluind),?a2);

id ga(a2?,?a1)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),g(a4?,p3?))=
ga(a3,li(gluind),?a1); *(?SIGN?)
id ga(?a1,a2?)*vrtx(ubar?(a3?, p1?),u?(a2?,p2?),g(a4?,p3?))=
ga(?a1,li(gluind),a3); *(?SIGN?)

id prop2(g(a1?,a2?,p1?))=gden(p1);

endrepeat;


*
* assign number to the lines with b and u respectively
*
if (occurs(Osb)=1);
id,once ga(?a1)=ga2(?a1);
endif;
if (occurs(Ouu)=1);
id,once ga(?a1)=ga1(?a1);
endif;

*
* Conjugate the Diagrams Di-> DiC
*

.sort
#do j=1,44
Hide D'j'OneLoop;
#enddo

#call conj;


*
* define the squared Matrix-Elements (1-Loop) x (Tree^*)
*

.sort
#do j=1,44
#do i=1,4
Local SQOneL'j'Tree'i' = D'j'OneLoop*D'i'treeC;
#enddo
#enddo
.sort
#do j=1,44
#do i=1,4
*Hide SQOneL'j'Tree'i';
Hide D'j'OneLoop;
Hide D'i'treeC;
Hide D'i'tree;
#enddo
#enddo
.sort
*Unhide SQOneL32Tree4;



*
* replace the fermionprops prop(q,p) by (pslash+m)/(p^2-m^2)
*

repeat;
id ga1?(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga1(?a1,p1,?a2)+mass(b)*ga1(?a1,?a2));

id ga1b(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga1b(?a1,p1,?a2)+mass(b)*ga1b(?a1,?a2));

id ga2(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga2(?a1,p1,?a2)+mass(b)*ga2(?a1,?a2));

id ga2b(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga2b(?a1,p1,?a2)+mass(b)*ga2b(?a1,?a2));
endrepeat;


*
* use spin sum: hel(X)= X*Xbar
* multiplied by helicity-factor hf(fermion) from averaged spin sum
* (1/2 for incoming, 1 for outgoing)
*

repeat;
id ga1(s?(p2?),?a2,b?(p1?))*ga1b(bar(b?(p1?)),?a4,bar(s?(p2?)))=hf(b)*hf(s)*ga1(?a2,hel(b(p1)),?a4,hel(s(p2)));
id ga2(s?(p2?),?a2,b?(p1?))*ga2b(bar(b?(p1?)),?a4,bar(s?(p2?)))=hf(b)*hf(s)*ga2(?a2,hel(b(p1)),?a4,hel(s(p2)));
endrepeat;

id hf(u)=1;
id hf(ubar)=1;
id hf(s)=1;
id hf(b)=1/2;

*
* operators-bar bar(O) := Oc
*

id ga1(?a1,bar(Ouu),?a2)=ga1(?a1,Ouuc,?a2);
id ga1(?a1,bar(Osb),?a2)=ga1(?a1,Osbc,?a2);
id ga2(?a1,bar(Ouu),?a2)=ga2(?a1,Ouuc,?a2);
id ga2(?a1,bar(Osb),?a2)=ga2(?a1,Osbc,?a2);

*
* replace ubar*u=hel(u) by p_u-m_u (factors of spin-sum: see above)
* (in massless case sign doesnt play role, BUT has to be adapted if mu,ms !=0)
*

repeat;
id ga1(?a1,hel(f?(p1?)),?a2)=ga1(?a1,p1,?a2)+mass(f)*ga1(?a1,?a2);
id ga2(?a1,hel(f?(p1?)),?a2)=ga2(?a1,p1,?a2)+mass(f)*ga2(?a1,?a2);
endrepeat;

*
* massless outgoing fermions s and u:
*

repeat;
id mass(b)^2=mb2;
endrepeat;
repeat;
id mass(s)=0;
id mass(u)=0;
id mass(ubar)=0;
endrepeat;

* "unpack" lorentz-indices
repeat;
id ga?(?a1,li(mu1?),?a3)=ga(?a1,mu1,?a3);
endrepeat;


* make ga1,2 from CF to F to use chainout
.sort
Function ga1,ga2;

*
* convert ga to dirac chains
*
* put in mu*PL and PR*mu
*
* IMPORTANT: mu*PL is only equivalent to PR*mu, if g5 anticommutes!!
*

chainout ga1;
id ga1(Ouu) = ga1(mu);
id ga1(Ouuc) = ga1(nu);
chainin ga1;

chainout ga2;
id ga2(Osb) = 1/2*(ga2(mu)-ga2(mu,five));
id ga2(Osbc) = 1/2*(ga2(nu)+ga2(five,nu));
chainin ga2;

id p(?a1)=1;

*
* LARIN SCHEME:
*
* replace TR(...mu.five...) by i/6*eps(mu,m1,m2,m3)*TR(...m1.m2.m3...):
*

* replace g5*g5 in trace by unit matrix:  [1610.09331]

id ga1(?mu1,five,five,?mu3)=ga1(?mu1,?mu3);
id ga2(?mu1,five,five,?mu3)=ga2(?mu1,?mu3);

* g5 occurs twice:

repeat;
id ga1(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps(mu2,dum1,dum2,dum3)*eps(mu4,dum4,dum5,dum6)*ga1(?mu1,dum1,dum2,dum3,?mu3,dum4,dum5,dum6,?mu5);
id ga2(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps(mu2,dum1,dum2,dum3)*eps(mu4,dum4,dum5,dum6)*ga2(?mu1,dum1,dum2,dum3,?mu3,dum4,dum5,dum6,?mu5);
endrepeat;

* g5 occurs once:

id ga1(?mu1,mu2?,five,?mu3)=-a1*i/6*eps(mu2,dum1,dum2,dum3)*ga2(?mu1,dum1,dum2,dum3,?mu3);
id ga2(?mu1,mu2?,five,?mu3)=-a1*i/6*eps(mu2,dum1,dum2,dum3)*ga2(?mu1,dum1,dum2,dum3,?mu3);


*
* Checked value and speed of internal trace algorithm vs. external!
* values are the same: 50s vs 9200s
*

chainout ga1;
repeat;
id ga1(mu1?)=g_(1,mu1);
endrepeat;

chainout ga2;
repeat;
id ga2(mu1?)=g_(2,mu1);
endrepeat;

Tracen,1;
Tracen,2;


#call Kin4body

*
* Simplify products of Epsilon-Tensors and the resulting metric tensors
*

#call EpsProd
#call Etasimp

* Elimination of p1

id eps(p1,p2?,p3?,p4?)=eps(q1,p2,p3,p4)+eps(q2,p2,p3,p4)+eps(q3,p2,p3,p4)+eps(q4,p2,p3,p4);

repeat;
id eps(q2,q3,q4,k1)=eps234k;
id eps(q1,q3,q4,k1)=eps134k;
id eps(q1,q2,q4,k1)=eps124k;
id eps(q1,q2,q3,k1)=eps123k;
id eps(q1,q2,q3,q4)=eps1234;
endrepeat;

*
* Kinematics
*

#call Kin4body

id i^2=-1;

* larin-replace is -a1*eps

Bracket den,gden;

Print +s;
.end

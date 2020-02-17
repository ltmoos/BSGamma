#procedure conj


*
* replace fermionline FL by FL*FLconj 
* ('do' loop does this for arbitrary length and the 'if' makes sure that the 
*  substitution is only done once for line 1 and 2)  
*

#do i=1,20
id ga1(<a1?>,...,<a'i'?>)=ga1b(<a'i'>,...,<a1>);
#enddo


#do i=1,20
id ga2(<a1?>,...,<a'i'?>)=ga2b(<a'i'>,...,<a1>);
#enddo

*
* bar spinors, operators, vertices and polarization vectors
*
repeat;
id ga1b(?a2,ubar(p1?),?a3)=ga1b(?a2,bar(ubar(p1)),?a3);
id ga1b(?a2,u(p1?),?a3)=ga1b(?a2,bar(u(p1)),?a3);
id ga1b(?a2,sbar(p1?),?a3)=ga1b(?a2,bar(sbar(p1)),?a3);
id ga1b(?a2,s(p1?),?a3)=ga1b(?a2,bar(s(p1)),?a3);
id ga1b(?a2,b(p1?),?a3)=ga1b(?a2,bar(b(p1)),?a3);
id ga1b(?a2,s(p1?),?a3)=ga1b(?a2,bar(s(p1)),?a3);
id ga1b(?a2,O1?,?a3)=ga1b(?a2,bar(O1),?a3);
id ga1b(?a2,prop2(?a1),?a3)=ga1b(?a2,bar(prop2(?a1)),?a3);
id ga1b(?a2,vp(?a1),?a3)=ga1b(?a2,bar(vp(?a1)),?a3);


id ga2b(?a2,ubar(p1?),?a3)=ga2b(?a2,bar(ubar(p1)),?a3);
id ga2b(?a2,u(p1?),?a3)=ga2b(?a2,bar(u(p1)),?a3);
id ga2b(?a2,sbar(p1?),?a3)=ga2b(?a2,bar(sbar(p1)),?a3);
id ga2b(?a2,s(p1?),?a3)=ga2b(?a2,bar(s(p1)),?a3);
id ga2b(?a2,b(p1?),?a3)=ga2b(?a2,bar(b(p1)),?a3);
id ga2b(?a2,s(p1?),?a3)=ga2b(?a2,bar(s(p1)),?a3);
id ga2b(?a2,O1?,?a3)=ga2b(?a2,bar(O1),?a3);
id ga2b(?a2,prop2(?a1),?a3)=ga2b(?a2,bar(prop2(?a1)),?a3);
id ga2b(?a2,vp(?a1),?a3)=ga2b(?a2,bar(vp(?a1)),?a3);

*id p(?a1)=p(?a1)*ppc(?a1);
id p(?a1)=1;
endrepeat;

#endprocedure 

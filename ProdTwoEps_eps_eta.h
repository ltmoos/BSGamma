#procedure EpsProd

*
* Rules for the product of 2 Epsilon-Tensors
* from -|Det of deltas|
* (all 4 indices same, D=4 -> -24)
* CAREFUL here, d_(a,b) is the kronecker-delta and summation d_(a,a) gives 4 not d, if not declared properly in FORM!
*

* 4 same

id eps(mu1?,mu2?,mu3?,mu4?)*eps(mu1?,mu2?,mu3?,mu4?) = -d*(d^3-6*d^2+11*d-6);
id eps1(mu1?,mu2?,mu3?,mu4?)*eps1(mu1?,mu2?,mu3?,mu4?) = -d*(d^3-6*d^2+11*d-6);
id eps2(mu1?,mu2?,mu3?,mu4?)*eps2(mu1?,mu2?,mu3?,mu4?) = -d*(d^3-6*d^2+11*d-6);

* 3 same

id eps(mu1?,mu2?,mu3?,mu4?)*eps(mu1?,mu2?,mu3?,mu5?)= -(d^3-6*d^2+11*d-6)*eta(mu4,mu5);
id eps1(mu1?,mu2?,mu3?,mu4?)*eps1(mu1?,mu2?,mu3?,mu5?)= -(d^3-6*d^2+11*d-6)*eta(mu4,mu5);
id eps2(mu1?,mu2?,mu3?,mu4?)*eps2(mu1?,mu2?,mu3?,mu5?)= -(d^3-6*d^2+11*d-6)*eta(mu4,mu5);

* 2 same

id eps(mu1?,mu2?,mu3?,mu4?)*eps(mu5?,mu6?,mu3?,mu4?)= (6-5*d+d^2) * (eta(mu1,mu6)*eta(mu2,mu5) - eta(mu1,mu5)*eta(mu2,mu6));
id eps1(mu1?,mu2?,mu3?,mu4?)*eps1(mu5?,mu6?,mu3?,mu4?)= (6-5*d+d^2) * (eta(mu1,mu6)*eta(mu2,mu5) - eta(mu1,mu5)*eta(mu2,mu6));
id eps2(mu1?,mu2?,mu3?,mu4?)*eps2(mu5?,mu6?,mu3?,mu4?)= (6-5*d+d^2) * (eta(mu1,mu6)*eta(mu2,mu5) - eta(mu1,mu5)*eta(mu2,mu6));

* 1 same

id eps(mu1?,mu2?,mu3?,mu4?)*eps(mu5?,mu6?,mu7?,mu4?)=(d-3)*(eta(mu1,mu7)*(eta(mu2,mu6)*eta(mu3,mu5)-eta(mu2,mu5)*eta(mu3,mu6))+eta(mu1,mu6)*(eta(mu2,mu5)* eta(mu3,mu7)-eta(mu2,mu7)*eta(mu3,mu5))+eta(mu1,mu5)*(eta(mu2,mu7)*eta(mu3,mu6)-eta(mu2,mu6)*eta(mu3,mu7)));
id eps1(mu1?,mu2?,mu3?,mu4?)*eps2(mu5?,mu6?,mu7?,mu4?)=(d-3)*(eta(mu1,mu7)*(eta(mu2,mu6)*eta(mu3,mu5)-eta(mu2,mu5)*eta(mu3,mu6))+eta(mu1,mu6)*(eta(mu2,mu5)* eta(mu3,mu7)-eta(mu2,mu7)*eta(mu3,mu5))+eta(mu1,mu5)*(eta(mu2,mu7)*eta(mu3,mu6)-eta(mu2,mu6)*eta(mu3,mu7)));
id eps2(mu1?,mu2?,mu3?,mu4?)*eps2(mu5?,mu6?,mu7?,mu4?)=(d-3)*(eta(mu1,mu7)*(eta(mu2,mu6)*eta(mu3,mu5)-eta(mu2,mu5)*eta(mu3,mu6))+eta(mu1,mu6)*(eta(mu2,mu5)* eta(mu3,mu7)-eta(mu2,mu7)*eta(mu3,mu5))+eta(mu1,mu5)*(eta(mu2,mu7)*eta(mu3,mu6)-eta(mu2,mu6)*eta(mu3,mu7)));


id eps(p1?,p2?,p3?,p4?)*eps1(p5?,p6?,p7?,p8?)=
-p8.p1*p7.p2*p6.p3*p5.p4+p8.p1*p7.p2*p5.p3*p6.p4+p8.p1*p6.p2*p7.p3*p5.p4
-p8.p1*p5.p2*p7.p3*p6.p4-p8.p1*p6.p2*p5.p3*p7.p4+p8.p1*p5.p2*p6.p3*p7.p4
+p7.p1*p8.p2*p6.p3*p5.p4-p7.p1*p8.p2*p5.p3*p6.p4-p6.p1*p8.p2*p7.p3*p5.p4
+p5.p1*p8.p2*p7.p3*p6.p4+p6.p1*p8.p2*p5.p3*p7.p4-p5.p1*p8.p2*p6.p3*p7.p4
-p7.p1*p6.p2*p8.p3*p5.p4+p7.p1*p5.p2*p8.p3*p6.p4+p6.p1*p7.p2*p8.p3*p5.p4
-p5.p1*p7.p2*p8.p3*p6.p4-p6.p1*p5.p2*p8.p3*p7.p4+p5.p1*p6.p2*p8.p3*p7.p4
+p7.p1*p6.p2*p5.p3*p8.p4-p7.p1*p5.p2*p6.p3*p8.p4-p6.p1*p7.p2*p5.p3*p8.p4
+p5.p1*p7.p2*p6.p3*p8.p4+p6.p1*p5.p2*p7.p3*p8.p4-p5.p1*p6.p2*p7.p3*p8.p4;

id eps1(p1?,p2?,p3?,p4?)*eps1(p5?,p6?,p7?,p8?)=
-p8.p1*p7.p2*p6.p3*p5.p4+p8.p1*p7.p2*p5.p3*p6.p4+p8.p1*p6.p2*p7.p3*p5.p4
-p8.p1*p5.p2*p7.p3*p6.p4-p8.p1*p6.p2*p5.p3*p7.p4+p8.p1*p5.p2*p6.p3*p7.p4
+p7.p1*p8.p2*p6.p3*p5.p4-p7.p1*p8.p2*p5.p3*p6.p4-p6.p1*p8.p2*p7.p3*p5.p4
+p5.p1*p8.p2*p7.p3*p6.p4+p6.p1*p8.p2*p5.p3*p7.p4-p5.p1*p8.p2*p6.p3*p7.p4
-p7.p1*p6.p2*p8.p3*p5.p4+p7.p1*p5.p2*p8.p3*p6.p4+p6.p1*p7.p2*p8.p3*p5.p4
-p5.p1*p7.p2*p8.p3*p6.p4-p6.p1*p5.p2*p8.p3*p7.p4+p5.p1*p6.p2*p8.p3*p7.p4
+p7.p1*p6.p2*p5.p3*p8.p4-p7.p1*p5.p2*p6.p3*p8.p4-p6.p1*p7.p2*p5.p3*p8.p4
+p5.p1*p7.p2*p6.p3*p8.p4+p6.p1*p5.p2*p7.p3*p8.p4-p5.p1*p6.p2*p7.p3*p8.p4;

id eps2(p1?,p2?,p3?,p4?)*eps2(p5?,p6?,p7?,p8?)=
-p8.p1*p7.p2*p6.p3*p5.p4+p8.p1*p7.p2*p5.p3*p6.p4+p8.p1*p6.p2*p7.p3*p5.p4
-p8.p1*p5.p2*p7.p3*p6.p4-p8.p1*p6.p2*p5.p3*p7.p4+p8.p1*p5.p2*p6.p3*p7.p4
+p7.p1*p8.p2*p6.p3*p5.p4-p7.p1*p8.p2*p5.p3*p6.p4-p6.p1*p8.p2*p7.p3*p5.p4
+p5.p1*p8.p2*p7.p3*p6.p4+p6.p1*p8.p2*p5.p3*p7.p4-p5.p1*p8.p2*p6.p3*p7.p4
-p7.p1*p6.p2*p8.p3*p5.p4+p7.p1*p5.p2*p8.p3*p6.p4+p6.p1*p7.p2*p8.p3*p5.p4
-p5.p1*p7.p2*p8.p3*p6.p4-p6.p1*p5.p2*p8.p3*p7.p4+p5.p1*p6.p2*p8.p3*p7.p4
+p7.p1*p6.p2*p5.p3*p8.p4-p7.p1*p5.p2*p6.p3*p8.p4-p6.p1*p7.p2*p5.p3*p8.p4
+p5.p1*p7.p2*p6.p3*p8.p4+p6.p1*p5.p2*p7.p3*p8.p4-p5.p1*p6.p2*p7.p3*p8.p4;


#endprocedure

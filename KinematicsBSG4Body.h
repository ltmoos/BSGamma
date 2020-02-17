#procedure Kin4body

id mb2=(s12+s13+s14+s23+s24+s34);
id p1=(q1+q2+q3+q4);

id q1.q1=0;
id q2.q2=0;
id q3.q3=0;
id q4.q4=0;

id k1.k1=k2;

id q1.k1=qk1;
id q2.k1=qk2;
id q3.k1=qk3;
id q4.k1=qk4;

id q1.q2=s12/2;
id q1.q3=s13/2;
id q1.q4=s14/2;
id q2.q3=s23/2;
id q2.q4=s24/2;
id q3.q4=s34/2;

#endprocedure

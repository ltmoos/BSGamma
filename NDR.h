#procedure NDR

*
* anticommute gamma5 in traces with an even number and use gamma5^2=1:
*

.sort
repeat;
id ga1?(?mu1,five,?mu2,five,?mu3)=(-1)**nargs_(?mu2)*ga1(?mu1,?mu2,?mu3);
endrepeat;

*
* Set traces with one gamma5 to zero (no products of two traces with single gamma5 in our calculations)
*

.sort
repeat;
id ga1?(?mu1,five,?mu2)=0;
endrepeat;
#endprocedure

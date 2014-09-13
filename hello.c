#include <stdio.h>

int some_function(int x)
{
int a,b,c;
int i = 2;
while(i<5)
{x=x+1;
a=x-2;
b=a+4;
c=b-2;
i++;
}
return 0;
}

int doit(int x,int y)
{
	int a;
        int d=0;
	//for(int j=0;j<5;j++)
        for(int i=0;i<4;i++)
        {
          //  if(d==0)
            d=x*y;
            a=x+y;
        }
        a=a+3;
        x=a+1;
        return a;
}


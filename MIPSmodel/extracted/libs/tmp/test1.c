void bit(int);
main()
{
  int val=15;
  printf("bitpattern is:");
  bit(val);
}
 
void bit(int n)
{
  int m,i;
  for(i=15; i>=0; i--)
    {
      m=1<<i;
      if((n&m)==0)
	{
	  printf("0");
	}
      else
	{
	  printf("1");
	}
    }
}

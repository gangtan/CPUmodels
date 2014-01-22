#include <stdio.h>
#include <bitset>

using namespace std;

int main()
{
    union
    {
      float input;   // assumes sizeof(float) == sizeof(int)
      int   output;
    }data;

    data.input = 2.25125;

    bitset<sizeof(float) * CHAR_BIT>   bits(data.output);


    cout << bits << endl;

}

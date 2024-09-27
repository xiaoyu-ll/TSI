#include <iostream>
#include<string>
#include <cstdlib>
using namespace std;
int main() {
    string choice;
    int op;

    std::cin >> choice;
    if(choice=="rids")
    op=1;
    else if(choice=="vtv")
    op=2;
    else if(choice=="ete")
    op=3;
    else if(choice=="eve")
    op=4;
    else
    {
        cout << "无效的选择，请重新运行程序。" << endl;
        return 0;
    }
    switch (op) {
        case 1:
            system("./rids_noorder");
            break;
        case 2:
            system("./vtv_noorder");
            break;
        case 3:
            system("./ete_noorder");
            break;
        case 4:
            system("./eve_noorder");
            break;
    }

    return 0;
}

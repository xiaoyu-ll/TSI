#include<iostream>
#include<fstream>
#include<sstream>
#include<string>
#include<algorithm>
#include<cmath>
#include<map>
#include<vector>
#include<stdlib.h>
#include <chrono>
#include <iomanip>
#include<stack>
#define maxn 3000000
using namespace std;
int daytab[2][13]={{0,31,28,31,30,31,30,31,31,30,31,30,31},{0,31,29,31,30,31,30,31,31,30,31,30,31}};
bool IsLeapYear(int year)
{
	return (year%4==0&&year%100!=0)||(year%400==0);
}
int sum(int year,int month,int day)//与2001年1月1日相差几天
{
    int count=0,row=IsLeapYear(year);
    while(year>2001)
    {
        year--;
        if(IsLeapYear(year))
        count+=366;
        else
        count+=365;
    }
    count+=day;
    for(int i=1;i<month;i++)
    count+=daytab[row][i];
    return count;
}
struct vertex//vg[maxn]
{
    int id;
    int indegree,outdegree;
    vector<int> adj1;//出边邻居结点
    vector<int> adje1;
    vector<int> adjt1;//相应发生的时间
    vector<int> adj2;//入边邻居结点
    vector<int> adje2;
    vector<int> adjt2;//相应发生的时间
};
struct vquery//vq[20]
{
    int id;
    int indegree,outdegree;
    vector<int> adj1;//邻居结点,出边
    vector<int> adje1;//邻接边，与adj的每一位置一一对应，可以从邻居结点对应上是哪条边
    vector<int> adj2;//邻居结点
    vector<int> adje2;
    bool flagt;//顶点是否存在时间限制
    int sm;//小边的类型，1代表出边，2代表入边
    int la;//大边的类型，1代表出边，2代表入边
    int vsm;//小边的另一顶点编号
    int vla;//大边的另一顶点编号
    int delta;
    bool flag;//判断是否已在matchorder中
    bool flag2;//判断是否是matchorder中某一顶点的邻结点
};
struct edge//eg[maxn]
{
    int id;//边的编号
    string source_id;// 边的起始顶点号，事务的发起方
    string target_id;//边的终结顶点号，事务的结束方
    string timestamp;//事务发生的时间
    int dur;//时间发生的日期与2020/1/1的距离
    //int amount;//事务的金额
    bool flag;
};
struct equery//eq[20]
{
    int id;
    string source_id;
    string target_id;
};
struct edgenode//enq[20],边结点，enq与eq是一一对应的
{
    int id;
    vector<int> adj;
    vector<int> adje;
    int indegree,outdegree;
    bool flag;//判断是否已在matchorder中
    bool flag2;//判断是否是matchorder中某一边结点的邻结点
};
struct edgeedge//eeq[20],连接边结点的边
{
    int id;
    int from,to;
};
struct edgever
{
    int id;
    int degree;
    vector<int> adj;
    bool flage;
};
struct edgetimecon//etc[20]存储有时间限制的不存在公共顶点的两边
{
    int eqn1,eqn2;//两条边的编号，小边，大边
    int timecon;//时间限制
    int vq1,vq2;//小边的源结点，大边的源结点
};
int temp=1;//判断是否把所有边结点加入生成树的全局变量
int ma=1;//指示当前在匹配哪条边，matchorder中的次序
int match_num=0;//记录有多少个匹配
int eq_num=0,vq_num=0,label_num=0;//query边数量，结点数量，标签种类
int v_num,e_num;////分别代表顶点数目和边数目,
int order=1;
int f=1,mm;
edge eg[maxn];//
vertex vg[maxn];
equery eq[20];//query的边集
vquery vq[20];//query的点集
edgetimecon etc[20];
edgenode enq[20];//query中的边转化为结点
edgeedge eeq[20];//连接query中相邻的边，类似最小生成树，边数等于结点数减一
edgeedge etq[20];//判断生成树是否有环
int me[20];//query相应边与待查询图中边的匹配数量
//int me[8]={0,10088,16788,19013,8114,25126,7030,6842};
int mt[20];//边的匹配顺序
int tm[20];//由order反求边
int timeconstrain[20][20];
int con_e[20];//记录每条边出现在时间限制组合中的次数
int matche[20];//边匹配结果
int matchv[20];//中间顶点匹配结果
int neibor[20];//形成matchorder的直接邻居
int neibor_can[20];//形成matchorder的候选邻居
int neiborsp[20];//直接邻居的种类，1代表由邻居指向该结点，2代表由该结点指向邻居
int neiborsp_can[20];//直接邻居种类的候选
map<string,string>lg;//账户对应的类型
map<string,string>lq;//query的顶点标签
string label[20];//query顶点的标签
int arrc;
int che[20];
map<int,int> vv;
int arr[20][6];//存储每一个组合，arr[i][1]为组合的第一条边,arr[i][2]为组合的第二,arr[i][3]为组中两条边的时间限制大小,arr[i][4]为组合中所有顶点都在order中出现的最小位置
vector< vector<int> > vec(20);//存储候选匹配边结点


void readedgelista()//读账户数据
{
    ifstream rda("dataset/college_msg.txt");
    //ifstream rda("dataset/email_eu.txt");
    //ifstream rda("dataset/stackoverflow.txt");
    //ifstream rda("dataset/mathoverflow.txt");
    //ifstream rda("dataset/ubuntu.txt");
    //ifstream rda("dataset/superuser.txt");
    //ifstream rda("dataset/wiki_talk.txt");
    if(!rda)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    //ofstream out("dataset/college_msg_20.txt");
    //ofstream out("dataset/college_msg_40.txt");
    //ofstream out("dataset/college_msg_60.txt");
    ofstream out("dataset/college_msg_80.txt");
    string ver,lab,tt;
    int count=0;
    while(rda>>ver>>lab>>tt)
    {
        //if(count%5==0)
        //if(count%5==0||count%5==1)
        //if(count%5==0||count%5==1||count%5==2)
        if(count%5==0||count%5==1||count%5==2||count%5==3)
        {
            out<<ver<<" "<<lab<<" "<<tt<<endl;
        }
        count++;
    }
    rda.close();
}





 
int main()
{
    
    readedgelista();//读账户信息数据
    return 0;
}
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
#define maxn 5000000
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
    vector<int> adjt1;//相应发生的时间
    vector<int> adj2;//入边邻居结点
    vector<int> adjt2;//相应发生的时间
};
struct vquery//vq[20]
{
    int id;
    int indegree,outdegree;
    vector<int> adj1;//邻居结点,出边
    //vector<int> adje1;//邻接边，与adj的每一位置一一对应，可以从邻居结点对应上是哪条边
    vector<int> adj2;//邻居结点
    //vector<int> adje2;
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
    //string timestamp;//事务发生的时间
    vector<int> dur;//时间发生的日期与2020/1/1的距离
    //int amount;//事务的金额
    bool flag;
};
struct equery//eq[20]
{
    int id;
    string source_id;
    string target_id;
};
struct edgetimecon//etc[20]存储有时间限制的不存在公共顶点的两边
{
    int eqn1,eqn2;//两条边的编号，小边，大边
    int timecon;//时间限制
    int vq1,vq2;//小边的源结点，大边的源结点
};
int temp=1;//判断是否把所有顶点加入matchorder的全局变量
int ma=1;//指示当前在匹配哪个边，matchorder中的次序
int match_num=0;//记录有多少个匹配
int etcn;//记录有多少对有时间限制但是没有公共端点的边
int eq_num=0,vq_num=0,label_num=0;//query边数量，结点数量，标签种类
int vg_num;//代表实际有用的顶点数
int v_num,e_num;////分别代表顶点数目和边数目,
int order=1;
int f=1,mm;
//edge eg[maxn];//
vertex vg[maxn];
int dm[20];
equery eq[20];//query的边集
vquery vq[20];//query的点集
edgetimecon etc[20];
edge etg[20];
int asc[20];//每个顶点所属组合数 $$
//int tic[20];//每个顶点时间受限的边数
int tvc[20];//记录点的时间受限的边数 $$
int mv[20];//query相应顶点与待查询图中顶点的匹配数量，pl[i]=mv[i]/v_num
//int me[8]={0,10088,16788,19013,8114,25126,7030,6842};
int mt[20];//边的匹配顺序
//int mt[20]={0,5,1,2,6,4,3};
int tm[20];//由order反求边
int match[20];//匹配结果
int neibor[20];//形成matchorder的直接邻居
int neibor_can[20];//形成matchorder的候选邻居
int neiborsp[20];//直接邻居的种类，1代表由邻居指向该结点，2代表由该结点指向邻居
int neiborsp_can[20];//直接邻居种类的候选
int timeconstrain[20][20];
map<string,string>lg;//账户对应的类型
map<string,string>lq;//query的顶点标签
string label[20];//query顶点的标签
vector< vector<int> > vec(20);//存储候选匹配顶点
int arr[20][5];//存储每一个组合，arr[i][1]为组合的第一个顶点,arr[i][1]为组合的第二个顶点,arr[i][3]为组合的第三个顶点,arr[i][4]为组合中所有顶点都在order中出现的最小位置
int arrc;//记录有多少个组合
string unixstamp_to_data(time_t unix_timestamp)
{
    // 将 Unix 时间戳转换为时间点
    chrono::system_clock::time_point time_point =std::chrono::system_clock::from_time_t(unix_timestamp);
    // 将时间点转换为本地时间
    time_t local_time = std::chrono::system_clock::to_time_t(time_point);
    // 将本地时间转换为可读的日期时间字符串
    stringstream ss;
    ss << std::put_time(std::localtime(&local_time), "%Y-%m-%d %H:%M:%S");
    string datetime_str=ss.str();
    return datetime_str;

}
string eq_mode(int e1,int e2,int &n)
{
    if(eq[e1].target_id==eq[e2].target_id)//共用一个目标结点
    {
        n=atoi(eq[e1].target_id.c_str());
        if(eq[e1].source_id==eq[e2].source_id)//并且共用一个源结点，两个顶点之间同向的两条边
        {
            if(timeconstrain[e1][e2]>0)
            return "211";
            else if(timeconstrain[e1][e2]<0)
            return "212";
            else
            return "213";
        }
        else
        {
            if(timeconstrain[e1][e2]>0)
            return "111";
            else if(timeconstrain[e1][e2]<0)
            return "112";
            else
            return "113";
        }
    }
    if(eq[e1].source_id==eq[e2].source_id)//共用一个源结点
    {
        n=atoi(eq[e1].source_id.c_str());
        if(eq[e1].target_id==eq[e2].target_id)//共用一个目标结点，两个顶点之间同向的两条边
        {
            if(timeconstrain[e1][e2]>0)
            return "221";
            else if(timeconstrain[e1][e2]<0)
            return "222";
            else
            return "223";
        }
        else
        {
            if(timeconstrain[e1][e2]>0)
            return "121";
            else if(timeconstrain[e1][e2]<0)
            return "122";
            else
            return "123";
        }
    }
    if(eq[e1].target_id==eq[e2].source_id)//e1的目标结点是e2的源结点
    {
        n=atoi(eq[e1].target_id.c_str());
        if(eq[e1].source_id==eq[e2].target_id)//并且e2的目标结点是e1的源结点，两个顶点之间相向的两条边
        {
            if(timeconstrain[e1][e2]>0)
            return "231";
            else if(timeconstrain[e1][e2]<0)
            return "232";
            else
            return "233";
        }
        else
        {
            if(timeconstrain[e1][e2]>0)
            return "131";
            else if(timeconstrain[e1][e2]<0)
            return "132";
            else
            return "133";
        }
    }
    if(eq[e1].source_id==eq[e2].target_id)//e1的源结点是e2的目标结点
    {
        n=atoi(eq[e2].target_id.c_str());
        if(eq[e1].target_id==eq[e2].source_id)//并且e1的目标结点是e2的源结点，两个顶点之间相向的两条边
        {
            if(timeconstrain[e1][e2]>0)
            return "241";
            else if(timeconstrain[e1][e2]<0)
            return "242";
            else
            return "243";
        }
        else
        {
            if(timeconstrain[e1][e2]>0)
            return "141";
            else if(timeconstrain[e1][e2]<0)
            return "142";
            else
            return "143";
        }
    }
    return "000";
}
void readquery()//读查询图的边，顶点标签，边的时序
{
    ifstream rd("query/r3tc2.txt");
    if(!rd)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    cout<<"read query1 successful!"<<endl;
    string a,b;
    int i=1,j=0,k=1,etci=1;//i是边序号
    while(rd>>a>>b)
    {
        cout<<a<<" "<<b<<endl;
        if(a=="|")
        break;
        eq[i].id=i;
        eq[i].source_id=a;
        eq[i].target_id=b;
        int ia=atoi(a.c_str());
        int ib=atoi(b.c_str());
        if(k<ia)
        k=ia;
        if(k<ib)
        k=ib;
        vq[ia].outdegree++;
        vq[ib].indegree++;
        vq[ia].adj1.push_back(ib);
        vq[ib].adj2.push_back(ia);
        vq[ia].flagt=false;
        vq[ib].flagt=false;
        vq[ia].flag=false;
        vq[ib].flag=false;
        vq[ia].flag2=false;
        vq[ib].flag2=false;
        i++;
    }
    string c,d;
    while(rd>>c>>d)
    {
        cout<<c<<" "<<d<<endl;
        if(c=="|")
        break;
        lq[c]=d;
        label[j++]=d;
    }
    string e,f;
    int g;
    while(rd>>e>>f>>g)
    {
        int k=1;
        cout<<e<<" "<<f<<" "<<g<<endl;
        int ia=atoi(e.c_str());//小边
        int ib=atoi(f.c_str());
        int ss=atoi(eq[ia].source_id.c_str());
        int st=atoi(eq[ia].target_id.c_str());
        int ls=atoi(eq[ib].source_id.c_str());
        int lt=atoi(eq[ib].target_id.c_str());
        timeconstrain[ia][ib]=g;
        timeconstrain[ib][ia]=-g;
        int join;
        string mode=eq_mode(ia,ib,join);
        if(mode[0]=='0')//两条边之间没有共同顶点
        {
            etc[etci].eqn1=ia;
            etc[etci].eqn2=ib;
            etc[etci].vq1=ss;
            etc[etci].vq2=ls;
            etc[etci].timecon=g;
            etci++;
        }
        else if(mode[0]=='2')//两个点之间的两条边
        {
            tvc[ss]++;
            tvc[st]++;
            tvc[ls]++;
            tvc[lt]++;
            if(mode[1]=='1')
            {
                if(mode[2]=='1'||mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=2;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=1;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                }
            }
            if(mode[1]=='2')
            {
                if(mode[2]=='1'||mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=1;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=2;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                }
            }
            if(mode[1]=='3')
            {
                if(mode[2]=='1')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=1;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=2;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                }
                else if(mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=1;
                    vq[st].la=2;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                    vq[ss].flagt=true;
                    vq[ss].sm=2;
                    vq[ss].la=1;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                }
            }
            if(mode[1]=='4')
            {
                if(mode[2]=='1')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=2;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=1;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                }   
                else if(mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=2;
                    vq[ss].la=1;
                    vq[ss].vsm=st;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                    vq[st].flagt=true;
                    vq[st].sm=1;
                    vq[st].la=2;
                    vq[st].vsm=ss;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                }
            }
        }
        else//mode[0]=1
        {
            tvc[ss]++;
            tvc[st]++;
            tvc[ls]++;
            tvc[lt]++;
            if(mode[1]=='1')
            {
                if(mode[2]=='1')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=2;
                    vq[st].vsm=ss;
                    vq[st].vla=ls;
                    vq[st].delta=g;
                    arr[k][1]=ss;
                    arr[k][2]=st;
                    arr[k][3]=ls;
                    k++;
                    asc[ss]++;
                    asc[st]++;
                    asc[ls]++;
                }
                else if(mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=2;
                    vq[st].vsm=ls;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                    arr[k][1]=ls;
                    arr[k][2]=st;
                    arr[k][3]=ss;
                    k++;
                    asc[ls]++;
                    asc[st]++;
                    asc[ss]++;
                }
            }
            if(mode[1]=='2')
            {
                if(mode[2]=='1')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=1;
                    vq[ss].vsm=st;
                    vq[ss].vla=lt;
                    vq[ss].delta=g;
                    arr[k][1]=st;
                    arr[k][2]=ss;
                    arr[k][3]=lt;
                    k++;
                    asc[st]++;
                    asc[ss]++;
                    asc[lt]++;
                }
                else if(mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=1;
                    vq[ss].vsm=lt;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
                    arr[k][1]=lt;
                    arr[k][2]=ss;
                    arr[k][3]=st;
                    k++;
                    asc[lt]++;
                    asc[ss]++;
                    asc[st]++;
                }
            }
            if(mode[1]=='3')
            {
                if(mode[2]=='1')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=1;
                    vq[st].vsm=ss;
                    vq[st].vla=lt;
                    vq[st].delta=g;
                    arr[k][1]=ss;
                    arr[k][2]=st;
                    arr[k][3]=lt;
                    k++;
                    asc[ss]++;
                    asc[st]++;
                    asc[lt]++;
                }
                else if(mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=1;
                    vq[st].la=2;
                    vq[st].vsm=lt;
                    vq[st].vla=ss;
                    vq[st].delta=g;
                    arr[k][1]=lt;
                    arr[k][2]=st;
                    arr[k][3]=ss;
                    k++;
                    asc[lt]++;
                    asc[st]++;
                    asc[ss]++;
                }
            }
            if(mode[1]=='4')
            {
                if(mode[2]=='1')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=2;
                    vq[ss].vsm=st;
                    vq[ss].vla=ls;
                    vq[ss].delta=g;
                    arr[k][1]=st;
                    arr[k][2]=ss;
                    arr[k][3]=ls;
                    k++;
                    asc[st]++;
                    asc[ss]++;
                    asc[ls]++;
                }
                else if(mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=2;
                    vq[ss].la=1;
                    vq[ss].vsm=ls;
                    vq[ss].vla=st;
                    vq[st].delta=g;
                    arr[k][1]=ls;
                    arr[k][2]=ss;
                    arr[k][3]=st;
                    k++;
                    asc[ls]++;
                    asc[ss]++;
                    asc[st]++;
                }
            }
        }
    }
    eq_num=i-1;
    vq_num=k;
    label_num=j-1;
    etcn=etci-1;
    arrc=k-1;
    rd.close();
}
void readedgelista()//读账户数据
{
    //ifstream rda("dataset/label_8.txt");
    //ifstream rda("dataset/email_eu_label.txt");
    //ifstream rda("dataset/stackoverflow_label.txt");
    //ifstream rda("dataset/mathoverflow_label.txt");
    ifstream rda("dataset/ubuntu_label.txt");
    //ifstream rda("dataset/superuser_label.txt");
    //ifstream rda("dataset/college_msg_label.txt");
    //ifstream rda("dataset/wiki_talk_label.txt");
    //ifstream rda("dataset/to_dataset_label.txt");
    if(!rda)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    cout<<"read label successful!"<<endl;
    string ver,lab;
    while(rda>>ver>>lab)
    {
        for(int i=0;i<vq_num;i++)
        {
            lab=lab.substr(0,1);
            if(lab==label[i])
            {
                lg[ver]=lab;
                break;
            }
        }
    }
    rda.close();
}
void readedgelistaa()//读转账数据
{
    //ifstream rdaa("dataset/stackoverflow_c2a.txt"); 
    // ifstream rdaa("dataset/stackoverflow_a2q.txt"); 
    //ifstream rdaa("dataset/ubuntu_a2q.txt"); 
    //ifstream rdaa("dataset/email_eu.txt"); 
    //ifstream rdaa("dataset/stackoverflow-c2a.txt"); 
    //ifstream rdaa("dataset/mathoverflow.txt"); 
    ifstream rdaa("dataset/ubuntu.txt"); 
    //ifstream rdaa("dataset/superuser.txt"); 
    //ifstream rdaa("dataset/college.txt");   
    //ifstream rdaa("dataset/wiki_talk.txt");
    //ifstream rdaa("dataset/to_dataset.txt");
    if(!rdaa)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    int i=1,k=0,s=0;
    string sn,tn,tsu,ts;
    while(rdaa>>sn>>tn>>tsu)
    {
        s++;
        if(s%5!=1)
        continue;
        else if(lg.count(sn)==0||lg.count(tn)==0)
        continue;
        else
        {
            int u2=atoi(tsu.c_str());
            time_t un=(time_t)u2;
            ts=unixstamp_to_data(un);
            string ye=ts.substr(0,4),mo=ts.substr(5,2),da=ts.substr(8,2);
            int year=atoi(ye.c_str()),mon=atoi(mo.c_str()),day=atoi(da.c_str());
            int si=atoi(sn.c_str());
            int ti=atoi(tn.c_str());
            if(k<si)
            k=si;
            if(k<ti)
            k=ti;
            vg[si].outdegree++;
            vg[ti].indegree++;
            vg[si].adj1.push_back(ti);
            vg[si].adjt1.push_back(sum(year,mon,day));
            vg[ti].adj2.push_back(si);
            vg[ti].adjt2.push_back(sum(year,mon,day));
            for(int j=1;j<=vq_num;j++)
            {
                if(lg[sn]==lq[to_string(j)])
                {
                    if(find(vec[j].begin(),vec[j].end(),si)==vec[j].end())
                    {
                        //mv[j]++;
                        vec[j].push_back(si);
                    }
                }
                else if(lg[tn]==lq[to_string(j)])
                {
                    if(find(vec[j].begin(),vec[j].end(),ti)==vec[j].end())
                    {
                        //mv[j]++;
                        vec[j].push_back(ti);
                    }
                }
            }
            i++;
        }
    }  
    cout<<"read graph g successful!"<<endl;
    e_num=i-1;
    v_num=k;
    rdaa.close();
}
bool prematch(int vvg,int dep)//判断能否与所有邻居匹配上，预匹配
{
    for(int i=0;i<vq[dep].adj1.size();i++)
    {
        bool vflag1=false;
        for(int j=0;j<vg[vvg].adj1.size();j++)
        {
            if(lg[to_string(vg[vvg].adj1[j])]==lq[to_string(vq[dep].adj1[i])])
            {
                vflag1=true;
                break;
            }
        }
        if(!vflag1)
        return false;
    }
    for(int i=0;i<vq[dep].adj2.size();i++)
    {
        bool vflag1=false;
        for(int j=0;j<vg[vvg].adj2.size();j++)
        {
            if(lg[to_string(vg[vvg].adj2[j])]==lq[to_string(vq[dep].adj2[i])])
            {
                vflag1=true;
                break;
            }
        }
        if(!vflag1)
        return false;
    }
    return true;
}
bool pretimecon(int vvg,int dep)//对于有时间限制的顶点先做时间限制预匹配
{
    int t1,t2;
    if(!vq[dep].flagt)
    return true;
    else
    {
        if(vq[dep].sm+vq[dep].la==2)
        {
            for(int j=0;j<vg[vvg].adj1.size();j++)
            {
                if(lg[to_string(vg[vvg].adj1[j])]==lq[to_string(vq[dep].vsm)])
                {
                    t1=vg[vvg].adjt1[j];
                    for(int k=0;k<vg[vvg].adj1.size();k++)
                    {
                        if(lg[to_string(vg[vvg].adj1[k])]==lq[to_string(vq[dep].vla)])
                        {
                            t2=vg[vvg].adjt1[k];
                            if(t2>t1&&(t2-t1)<vq[dep].delta)
                            return true;
                        }
                    }
                }
            }
        }
        else if(vq[dep].sm+vq[dep].la==4)
        {
            for(int j=0;j<vg[vvg].adj2.size();j++)
            {
                if(lg[to_string(vg[vvg].adj2[j])]==lq[to_string(vq[dep].vsm)])
                {
                    t1=vg[vvg].adjt2[j];
                    for(int k=0;k<vg[vvg].adj2.size();k++)
                    {
                        if(lg[to_string(vg[vvg].adj2[k])]==lq[to_string(vq[dep].vla)])
                        {
                            t2=vg[vvg].adjt2[k];
                            if(t2>t1&&(t2-t1)<vq[dep].delta)
                            return true;
                        }
                    }
                }
            }
        }
        else
        {
            if(vq[dep].sm==1)//小边是出边
            {
                for(int j=0;j<vg[vvg].adj1.size();j++)
                {
                    if(lg[to_string(vg[vvg].adj1[j])]==lq[to_string(vq[dep].vsm)])
                    {
                        t1=vg[vvg].adjt1[j];
                        for(int k=0;k<vg[vvg].adj2.size();k++)
                        {
                            if(lg[to_string(vg[vvg].adj2[k])]==lq[to_string(vq[dep].vla)])
                            {
                                t2=vg[vvg].adjt2[k];
                                if(t2>t1&&(t2-t1)<vq[dep].delta)
                                return true;
                            }
                        }
                    }
                }
            }
            else
            {
                for(int j=0;j<vg[vvg].adj2.size();j++)
                {
                    if(lg[to_string(vg[vvg].adj2[j])]==lq[to_string(vq[dep].vsm)])
                    {
                        t1=vg[vvg].adjt2[j];
                        for(int k=0;k<vg[vvg].adj1.size();k++)
                        {
                            if(lg[to_string(vg[vvg].adj1[k])]==lq[to_string(vq[dep].vla)])
                            {
                                t2=vg[vvg].adjt1[k];
                                if(t2>t1&&(t2-t1)<vq[dep].delta)
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    return false;
}
void can_order()
{
    for(int i=0;i<vq[f].adj1.size();i++)
    {
        vq[vq[f].adj1[i]].flag2=true;
        dm[vq[f].adj1[i]]++;
        if(neibor_can[vq[f].adj1[i]]==0)
        {
            neibor_can[vq[f].adj1[i]]=order-1;
            neiborsp_can[vq[f].adj1[i]]=1;
        }
    }
    for(int i=0;i<vq[f].adj2.size();i++)
    {
        vq[vq[f].adj2[i]].flag2=true;
        dm[vq[f].adj2[i]]++;
        if(neibor_can[vq[f].adj2[i]]==0)
        {
            neibor_can[vq[f].adj2[i]]=order-1;
            neiborsp_can[vq[f].adj2[i]]=2;
        }
    }
    int dmax=0;
    for(int i=1;i<=vq_num;i++)
    {
        if(dmax<dm[i]&&!vq[i].flag)
        dmax=dm[i];
    }
    vector<int> can;//本次选顶点的候选顶点
    for(int i=1;i<=vq_num;i++)
    {
        if(!vq[i].flag&&vq[i].flag2&&dm[i]==dmax)
        can.push_back(i);
    }
    mm=mv[can[0]];
    f=can[0];
    for(int j=1;j<can.size();j++)
    {
        if(mm<mv[can[j]])
        {
            mm=mv[can[j]];
            f=can[j];
        }
    }
    mt[order++]=f;
    tm[f]=order-1;
    neibor[f]=neibor_can[f];
    neiborsp[f]=neiborsp_can[f];
    vq[f].flag=true;
}
void matchorder()
{
    for(int i=1;i<=vq_num;i++)//准备工作
    {
        for(int j=0;j<vec[i].size();j++)//出度入度或预匹配不匹配，直接剪掉
        {
            if(vg[vec[i][j]].indegree<vq[i].indegree||vg[vec[i][j]].outdegree<vq[i].outdegree||!prematch(vec[i][j],i)||!pretimecon(vec[i][j],i))
            {
                vec[i].erase(vec[i].begin()+j);
                j--;
            }
        }
    }
    for(int i=1;i<=vq_num;i++)//准备工作
    mv[i]=asc[i]+tvc[i];
    mm=mv[1];
    f=1;
    for(int i=2;i<=vq_num;i++)
    {
        if(mm<mv[i])
        {
            mm=mv[i];
            f=i;
        }
    }
    mt[order++]=f;//第一个匹配的顶点
    tm[f]=order-1;
    vq[f].flag=true;
    int kk=vq_num-1;
    while(kk--)
    {
        for(int i=1;i<=vq_num;i++)
        dm[i]=0;
        can_order();
    }
    for(int i=1;i<=arrc;i++)
    {
        int count=0;
        for(int j=1;j<=vq_num;j++)
        {
            if(mt[j]==arr[i][1]||mt[j]==arr[i][2]||mt[j]==arr[i][3])
            count++;
            if(count==3)
            {
                arr[i][4]=j;
                break;
            }
        }
    }
}
bool timecon()
{
    int t1,t2;
    for(int i=1;i<eq_num;i++)
    {
        for(int j=i+1;j<=eq_num;j++)
        {
            if(timeconstrain[i][j]>0)
            {
                bool tflag=false;
                for(int k=0;k<etg[j].dur.size();k++)
                {
                    t2=etg[j].dur[k];
                    for(int l=0;l<etg[i].dur.size();l++)
                    {
                        t1=etg[i].dur[l];
                        if((t2-t1)<=timeconstrain[i][j]&&t2>t1)
                        {
                            tflag=true;
                            break;
                        }
                    }
                }
                if(!tflag)
                return false;
            }
            else if(timeconstrain[i][j]<0)
            {
                bool tflag=false;
                for(int k=0;k<etg[i].dur.size();k++)
                {
                    t2=etg[i].dur[k];
                    for(int l=0;l<etg[j].dur.size();l++)
                    {
                        t1=etg[j].dur[l];
                        if((t2-t1)<=timeconstrain[j][i]&&t2>t1)
                        {
                            tflag=true;
                            break;
                        }
                    }
                }
                if(!tflag)
                return false;
            }
        }
    }
    return true;
}   
bool astimematch(int v,int vsm,int vla)
{
    int or1=tm[v],or2=tm[vsm],or3=tm[vla];
    int t1,t2;
    if(vq[v].sm+vq[v].la==2)
    {
        for(int j=0;j<vg[match[or1]].adj1.size();j++)
        {
            if(vg[match[or1]].adj1[j]==match[or2])
            {
                t1=vg[match[or1]].adjt1[j];
                for(int k=0;k<vg[match[or1]].adj1.size();k++)
                {
                    if(vg[match[or1]].adj1[k]==match[or3])
                    {
                        t2=vg[match[or1]].adjt1[k];
                        //if(t2>t1&&(t2-t1)<=vq[v].delta)
                        if(t2>t1)
                        return true;
                    }
                }
            }
        }
    }
    else if(vq[v].sm+vq[v].la==4)
    {
        for(int j=0;j<vg[match[or1]].adj2.size();j++)
        {
            if(vg[match[or1]].adj2[j]==match[or2])
            {
                t1=vg[match[or1]].adjt2[j];
                for(int k=0;k<vg[match[or1]].adj2.size();k++)
                {
                    if(vg[match[or1]].adj2[k]==match[or3])
                    {
                        t2=vg[match[or1]].adjt2[k];
                        //if(t2>t1&&(t2-t1)<=vq[v].delta)
                        if(t2>t1)
                        return true;
                    }
                }
            }
        }
    }
    else
    {
        if(vq[v].sm==1)
        {
            for(int j=0;j<vg[match[or1]].adj1.size();j++)
            {
                if(vg[match[or1]].adj1[j]==match[or2])
                {
                    t1=vg[match[or1]].adjt1[j];
                    for(int k=0;k<vg[match[or1]].adj2.size();k++)
                    {
                        if(vg[match[or1]].adj2[k]==match[or3])
                        {
                            t2=vg[match[or1]].adjt2[k];
                            //if(t2>t1&&(t2-t1)<=vq[v].delta)
                            if(t2>t1)
                            return true;
                        }
                    }
                }
            }
        }
        else
        {
            for(int j=0;j<vg[match[or1]].adj2.size();j++)
            {
                if(vg[match[or1]].adj2[j]==match[or2])
                {
                    t1=vg[match[or1]].adjt2[j];
                    for(int k=0;k<vg[match[or1]].adj1.size();k++)
                    {
                        if(vg[match[or1]].adj1[k]==match[or3])
                        {
                            t2=vg[match[or1]].adjt1[k];
                            //if(t2>t1&&(t2-t1)<=vq[v].delta)
                            if(t2>t1)
                            return true;
                        }
                    }
                }
            }
        }
    }
    return false;
}
void expandmatching(int dep)
{
    if(dep==vq_num+1)//已经形成一个匹配结果
    {           
        for(int i=1;i<=eq_num;i++)    
        {
            etg[i].id=i;
            int si=atoi(eq[i].source_id.c_str());
            int ti=atoi(eq[i].target_id.c_str());
            etg[i].dur.clear();
            for(int j=0;j<vg[match[tm[si]]].adj1.size();j++)
            {
                if(vg[match[tm[si]]].adj1[j]==match[tm[ti]])
                etg[i].dur.push_back(vg[match[tm[si]]].adjt1[j]);
            }
        }              
        if(timecon())
        {
            match_num++;
            cout<<match_num<<":";
            for(int j=1;j<=vq_num;j++)    
            cout<<match[j]<<" ";
            cout<<endl;
        } 
    }
    else//还没形成一个匹配
    {
        vec[mt[dep]].clear();
        bool vflag=true;
        int diradj=neibor[mt[dep]];//该轮匹配顶点的直接邻居的匹配order
        if(neiborsp[mt[dep]]==1)//该顶点是直接邻居的出边
        {
            for(int j=0;j<vg[match[diradj]].adj1.size();j++)
            {
                int vvg=vg[match[diradj]].adj1[j];
                //if(lg[to_string(vvg)]==lq[to_string(mt[dep])]&&vg[vvg].indegree>=vq[mt[dep]].indegree&&vg[vvg].outdegree>=vq[mt[dep]].outdegree&&prematch(vvg,mt[dep])&&pretimecon(vvg,mt[dep]))
                if(lg[to_string(vvg)]==lq[to_string(mt[dep])]&&vg[vvg].indegree>=vq[mt[dep]].indegree&&vg[vvg].outdegree>=vq[mt[dep]].outdegree)
                {//标签和出入度和预匹配能对应上
                    if(find(vec[mt[dep]].begin(),vec[mt[dep]].end(),vvg)==vec[mt[dep]].end())
                    vec[mt[dep]].push_back(vvg);
                }
            }
        }
        else if(neiborsp[mt[dep]]==2)
        {
            for(int j=0;j<vg[match[diradj]].adj2.size();j++)
            {
                int vvg=vg[match[diradj]].adj2[j];
                //if(lg[to_string(vvg)]==lq[to_string(mt[dep])]&&vg[vvg].indegree>=vq[mt[dep]].indegree&&vg[vvg].outdegree>=vq[mt[dep]].outdegree&&prematch(vvg,mt[dep])&&pretimecon(vvg,mt[dep]))
                if(lg[to_string(vvg)]==lq[to_string(mt[dep])]&&vg[vvg].indegree>=vq[mt[dep]].indegree&&vg[vvg].outdegree>=vq[mt[dep]].outdegree)
                {
                    if(find(vec[mt[dep]].begin(),vec[mt[dep]].end(),vvg)==vec[mt[dep]].end())
                    vec[mt[dep]].push_back(vvg);
                }  
            }
        }
        for(int j=0;j<vec[mt[dep]].size();j++)
        {//判断与已经匹配的顶点是否能匹配上
            bool vflag=true;
            int vt=vec[mt[dep]][j];
            for(int k=0;k<vq[mt[dep]].adj1.size();k++)
            {
                if(tm[vq[mt[dep]].adj1[k]]<dep)
                {
                    bool vflag1=false;
                    for(int l=0;l<vg[vt].adj1.size();l++)
                    {
                        if(match[tm[vq[mt[dep]].adj1[k]]]==vg[vt].adj1[l])
                        {
                            vflag1=true;
                            break;
                        }
                    }
                    if(!vflag1)
                    {
                        vflag=false;
                        break;
                    }
                }
            }
            if(!vflag)
            continue;
            for(int k=0;k<vq[mt[dep]].adj2.size();k++)
            {//判断与已经匹配的顶点是否能匹配上
                if(tm[vq[mt[dep]].adj2[k]]<dep)
                {
                    bool vflag1=false;
                    for(int l=0;l<vg[vt].adj2.size();l++)
                    {
                        if(match[tm[vq[mt[dep]].adj2[k]]]==vg[vt].adj2[l])
                        {
                            vflag1=true;
                            break;
                        }
                    }
                    if(!vflag1)
                    {
                        vflag=false;
                        break;
                    }
                }
            }
            if(!vflag)
            continue;
            else
            {
                match[dep]=vt;
                bool tflag=true;
                for(int l=1;l<=arrc;l++)
                {   
                    if(arr[l][4]==dep)
                    {
                        bool tflag1=false;
                        if(astimematch(arr[l][2],arr[l][1],arr[l][3]))
                        tflag1=true;
                        if(!tflag1)
                        {
                            tflag=false;
                            break;
                        }
                    }   
                }
                if(tflag)
                {
                    //match[dep]=vt;
                    expandmatching(dep+1);
                }
            }
        } 
    }
}
void pamt()
{
    for(int j=2;j<=vq_num;j++)//除了第一个顶点的候选匹配，清除其余顶点的候选匹配
    vec[mt[j]].clear();
    //顶点的标签已经匹配上了，出入度也符合，预匹配也符合语义符合   匹配每一条边
    for(int k=0;k<vec[mt[1]].size();k++)//匹配matchorder中的第一条边
    {
        ma=1;
        match[ma++]=vec[mt[1]][k];
        expandmatching(ma);
    }
}
int main()
{
    clock_t start_time, end_time;//由邻居生成候选，标签，出入度，预匹配剪枝有时间限制的顶点先剪枝，加入了时间的预匹配，形成匹配后判断时间限制
    
    readquery();//读query
    for(int j=0;j<=vq_num;j++)
    {
        string str=to_string(j);
        cout<<lq[str]<<endl;
    }
    readedgelista();//读账户信息数据
    readedgelistaa();//读账户间转账数据
    start_time = clock();
    matchorder();
    pamt();
    end_time = clock();     //获取结束时间
    double Times = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    cout<<Times<<"seconds"<<endl;
    return 0;
}
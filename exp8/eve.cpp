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
int mav=1;
int mtemp=1;
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
int mtv[20];//边匹配中间点点匹配顺序
int tm[20];//由order反求边
int tmv[20];//由order反求点
int con_e[20];//记录每条边出现在时间限制组合中的次数
int timeconstrain[20][20];
int matche[20];//边匹配结果
int matchv[20];//中间顶点匹配结果
int neibor[20];//形成matchorder的直接邻居
int neibor_can[20];//形成matchorder的候选邻居
int neiborsp[20];//直接邻居的种类，1代表由邻居指向该结点，2代表由该结点指向邻居
int neiborsp_can[20];//直接邻居种类的候选
map<string,string>lg;//账户对应的类型
map<string,string>lq;//query的顶点标签
string label[20];//query顶点的标签
map<int,int> vbf;
int arrc;
int arr[20][6];//存储每一个组合，arr[i][1]为组合的第一条边,arr[i][2]为组合的第二,arr[i][3]为组中两条边的时间限制大小,arr[i][4]为组合中所有顶点都在order中出现的最小位置
vector< vector<int> > vec(20);//存储候选匹配边结点
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
    ifstream rd("query/ql4.txt");
    if(!rd)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    cout<<"read query successful!"<<endl;
    string a,b;
    int i=1,j=0,k=0,etci=1,cou=1;//i是边序号
    while(rd>>a>>b)
    {
        cout<<a<<" "<<b<<endl;
        if(a=="|")
        break;
        eq[i].id=i;
        eq[i].source_id=a;
        eq[i].target_id=b;
        enq[i].id=i;
        enq[i].flag=false;
        enq[i].flag2=false;
        int ia=atoi(a.c_str());
        int ib=atoi(b.c_str());
        if(k<ia)
        k=ia;
        if(k<ib)
        k=ib;
        vq[ia].outdegree++;
        vq[ib].indegree++;
        vq[ia].adj1.push_back(ib);
        vq[ia].adje1.push_back(i);
        vq[ib].adj2.push_back(ia);
        vq[ib].adje2.push_back(i);
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
    for(int k=0;k<i;k++)
    con_e[k]=0;
    while(rd>>e>>f>>g)
    {
        cout<<e<<" "<<f<<" "<<g<<endl;
        int ia=atoi(e.c_str());
        int ib=atoi(f.c_str());
        con_e[ia]++;
        con_e[ib]++;
        timeconstrain[ia][ib]=g;
        timeconstrain[ib][ia]=-g;
        int ss=atoi(eq[ia].source_id.c_str());
        int st=atoi(eq[ia].target_id.c_str());
        int ls=atoi(eq[ib].source_id.c_str());
        int lt=atoi(eq[ib].target_id.c_str());
        arr[cou][1]=ia;
        arr[cou][2]=ib;
        arr[cou][3]=g;
        int join;
        string mode=eq_mode(ia,ib,join);
        arr[cou][5]=join;
        cou++;
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
                }
                else if(mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=2;
                    vq[st].la=2;
                    vq[st].vsm=ls;
                    vq[st].vla=ss;
                    vq[st].delta=g;
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
                }
                else if(mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=1;
                    vq[ss].la=1;
                    vq[ss].vsm=lt;
                    vq[ss].vla=st;
                    vq[ss].delta=g;
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
                }
                else if(mode[2]=='2')
                {
                    vq[st].flagt=true;
                    vq[st].sm=1;
                    vq[st].la=2;
                    vq[st].vsm=lt;
                    vq[st].vla=ss;
                    vq[st].delta=g;
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
                }
                else if(mode[2]=='2')
                {
                    vq[ss].flagt=true;
                    vq[ss].sm=2;
                    vq[ss].la=1;
                    vq[ss].vsm=ls;
                    vq[ss].vla=st;
                    vq[st].delta=g;
                }
            }
        }
    }
    eq_num=i-1;
    vq_num=k;
    label_num=j-1;
    arrc=cou-1;
    rd.close();
}
void creatforest()
{
    for(int i=1;i<=vq_num;i++)//遍历所有顶点
    {
        vector<int> ve;
        ve.insert(ve.end(),vq[i].adje1.begin(),vq[i].adje1.end());
        ve.insert(ve.end(),vq[i].adje2.begin(),vq[i].adje2.end());
        int si=ve.size();
        cout<<i<<" "<<si<<endl;
        for(int j=0;j<si;j++)
        cout<<ve[j]<<" ";
        cout<<endl;
        for(int j=0;j<si;j++)
        {
            for(int k=0;k<si;k++)
            {
                if(j==k)//
                continue;
                if(timeconstrain[ve[j]][ve[k]]>0)
                {
                    eeq[temp].from=ve[j];
                    eeq[temp].to=ve[k];
                    enq[ve[j]].outdegree++;
                    enq[ve[k]].indegree++;
                    enq[ve[j]].adj.push_back(ve[k]);
                    enq[ve[j]].adje.push_back(temp);
                    enq[ve[k]].adj.push_back(ve[j]);
                    enq[ve[k]].adje.push_back(temp);
                    temp++;
                    //判断是否有环
                    edgever entq[eq_num+1];
                    for(int kk=1;kk<=eq_num;kk++)
                    {
                        entq[kk].flage=true;
                        entq[kk].id=enq[kk].id;
                        entq[kk].degree=enq[kk].indegree+enq[kk].outdegree;
                        entq[kk].adj.insert(entq[kk].adj.end(),enq[kk].adj.begin(),enq[kk].adj.end());
                    }
                    int del=0;//记录删除了几个顶点
                    int coun=0;//记录度<=1的顶点个数
                    for(int l=1;l<=eq_num;l++)
                    {
                        if(entq[l].degree<=1)
                        {
                            coun++;
                            break;
                        }
                    }
                    while(coun)
                    {
                        for(int l=1;l<=eq_num;l++)
                        {
                            if(entq[l].flage&&entq[l].degree<=1)
                            {
                                entq[l].flage=false;//删除了顶点l
                                del++;
                                for(int ll=0;ll<entq[l].adj.size();ll++)
                                {
                                    int vadj=entq[l].adj[ll];
                                    entq[vadj].degree--;
                                    for(int kl=0;kl<entq[vadj].adj.size();kl++)
                                    {
                                        if(entq[vadj].adj[kl]==l)
                                        entq[vadj].adj.erase(entq[vadj].adj.begin()+kl);
                                    }
                                }
                            }
                        }
                        coun=0;
                        for(int l=1;l<=eq_num;l++)
                        {
                            if(entq[l].flage&&entq[l].degree<=1)
                            coun++;
                        }
                    }
                    if(del<eq_num)//如果加入这条边成环了，则不加入这条边
                    {
                        temp--;
                        enq[ve[j]].outdegree--;
                        enq[ve[k]].indegree--;
                        enq[ve[j]].adj.pop_back();
                        enq[ve[j]].adje.pop_back();
                        enq[ve[k]].adj.pop_back();
                        enq[ve[k]].adje.pop_back();
                    }
                }    
            }
        }
    }
}      
void readedgelista()//读账户数据
{
    //ifstream rda("dataset/label_24.txt");
    //ifstream rda("dataset/email_eu_label.txt");
    //ifstream rda("dataset/college_msg_label.txt");
    //ifstream rda("dataset/stackoverflow_label.txt");
    //ifstream rda("dataset/mathoverflow_label.txt");
    ifstream rda("dataset/ubuntu_label.txt");
    //ifstream rda("dataset/superuser_label.txt");
    //ifstream rda("dataset/wiki_talk_label.txt");
    //ifstream rda("dataset/label.txt");
    //ifstream rda("dataset/to_dataset_label.txt");
    if(!rda)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    string ver,lab;
    while(rda>>ver>>lab)
    {
        for(int i=0;i<=vq_num;i++)
        {
            lab=lab.substr(0,1);
            if(lab==label[i])
            {
                lg[ver]=lab;
                break;
            }
        }
    }
    cout<<"read label successful!"<<endl;
    rda.close();
}
void readedgelistaa()//读转账数据
{
    //ifstream rdaa("dataset/ubuntu_a2q.txt");
    //ifstream rdaa("dataset/email_eu.txt");
    //ifstream rdaa("dataset/stackoverflow-a2q.txt");
    //ifstream rdaa("dataset/mathoverflow.txt");
    ifstream rdaa("dataset/ubuntu.txt");
    //ifstream rdaa("dataset/superuser.txt");
    //ifstream rdaa("dataset/college.txt");ifstream rdaa("dataset/wiki_talk.txt");
    //ifstream rdaa("dataset/evedataset.txt");
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
        //if(s%5!=1&&s%5!=2&&s%5!=3&&s%5!=4)
        //continue;
        if(lg.count(sn)==0||lg.count(tn)==0)
        continue;
        else
        {
            eg[i].id=i;
            eg[i].source_id=sn;
            eg[i].target_id=tn;
            int u2=atoi(tsu.c_str());
            time_t un=(time_t)u2;
            ts=unixstamp_to_data(un);
            eg[i].timestamp=ts;
            string ye=ts.substr(0,4),mo=ts.substr(5,2),da=ts.substr(8,2);
            int year=atoi(ye.c_str()),mon=atoi(mo.c_str()),day=atoi(da.c_str());
            eg[i].dur=sum(year,mon,day);
            for(int j=1;j<=eq_num;j++)
            {
                if(lg[sn]==lq[eq[j].source_id]&&lg[tn]==lq[eq[j].target_id])
                {
                    me[j]++;
                    vec[j].push_back(i);
                }
            }
            int si=atoi(sn.c_str());
            int ti=atoi(tn.c_str());
            if(k<si)
            k=si;
            if(k<ti)
            k=ti;
            vg[si].outdegree++;
            vg[ti].indegree++;
            vg[si].adj1.push_back(ti);
            vg[si].adje1.push_back(i);
            vg[si].adjt1.push_back(sum(year,mon,day));
            vg[ti].adj2.push_back(si);
            vg[ti].adje2.push_back(i);
            vg[ti].adjt2.push_back(sum(year,mon,day));
            i++;
        }
    }  
    e_num=i-1;//75463
    v_num=k;
    cout<<"read graph g successful!"<<endl;
    rdaa.close();
    cout<<"k="<<k<<endl;
}
void cluster_join()//
{
    if(order==1)
    {
        bool tieflag=false;
        int mf;
        for(int j=2;j<=eq_num;j++)
        {
            if(mm<con_e[j])
            {
                mm=con_e[j];
                f=j;
                tieflag=false;
                mf=me[j];
            }
            else if(mm==con_e[j])
            {
                tieflag=true;
            }
        }
        if(!tieflag)
        mt[order++]=f;//第一条匹配的边
        else
        {
            for(int j=1;j<=eq_num;j++)
            {
                if(mm==con_e[j])
                {
                    if(mf>me[j])
                    {
                        mf=me[j];
                        f=j;
                    }
                }
            }
            mt[order++]=f;
        }
        tm[f]=order-1;
        enq[f].flag=true;
        enq[f].flag2=true;
    }
    else
    {
        vector<int> can;//即将加入matchorder的候选边结点
        for(int j=1;j<order;j++)
        {
            string sn=eq[mt[j]].source_id;
            int isn=atoi(sn.c_str());
            string tn=eq[mt[j]].target_id;
            int itn=atoi(tn.c_str());
            for(int jk=0;jk<vq[isn].adje1.size();jk++)
            {
                if((!enq[vq[isn].adje1[jk]].flag)&&find(can.begin(),can.end(),vq[isn].adje1[jk])==can.end())
                {
                    can.push_back(vq[isn].adje1[jk]);
                    neibor_can[vq[isn].adje1[jk]]=j;
                }
            }
            for(int jk=0;jk<vq[isn].adje2.size();jk++)
            {
                if((!enq[vq[isn].adje2[jk]].flag)&&find(can.begin(),can.end(),vq[isn].adje2[jk])==can.end())
                {
                    can.push_back(vq[isn].adje2[jk]);
                    neibor_can[vq[isn].adje2[jk]]=j;
                }
            }
            for(int jk=0;jk<vq[itn].adje1.size();jk++)
            {
                if((!enq[vq[itn].adje1[jk]].flag)&&find(can.begin(),can.end(),vq[itn].adje1[jk])==can.end())
                {
                    can.push_back(vq[itn].adje1[jk]);
                    neibor_can[vq[itn].adje1[jk]]=j;
                }
            }
            for(int jk=0;jk<vq[itn].adje2.size();jk++)
            {
                if((!enq[vq[itn].adje2[jk]].flag)&&find(can.begin(),can.end(),vq[itn].adje2[jk])==can.end())
                {
                    can.push_back(vq[itn].adje2[jk]);
                    neibor_can[vq[itn].adje2[jk]]=j;
                }
            }
        }
        mm=con_e[can[0]];
        f=can[0];
        bool tieflag=false;
        int mf;
        for(int j=1;j<can.size();j++)
        {
            if(con_e[can[j]]>mm)
            {
                mm=con_e[can[j]];
                f=can[j];
                tieflag=false;
                mf=me[can[j]];
            }
            else if(mm==con_e[can[j]])
            {
                tieflag=true;
            }
        }
        if(!tieflag)
        mt[order++]=f;
        else
        {
            for(int j=0;j<can.size();j++)
            {
                if(mm==con_e[can[j]])
                {
                    if(mf>me[can[j]])
                    {
                        mf=me[can[j]];
                        f=can[j];
                    }
                }
            }
            mt[order++]=f;
        }
        tm[f]=order-1;
        enq[f].flag=true;
        enq[f].flag2=true;
        neibor[f]=neibor_can[f];
    }
}
void cluster_order()
{
    vector<int> can;
    for(int j=0;j<enq[f].adj.size();j++)//
    {
        enq[enq[f].adj[j]].flag2=true;
        if(enq[enq[f].adj[j]].flag2&&!enq[enq[f].adj[j]].flag)
        can.push_back(enq[f].adj[j]);
        neibor_can[enq[f].adj[j]]=order-1;//邻居结点直接是matchorder中的顺序
    }
    int kk=enq[f].adj.size();
    while(kk--)
    {
        int pos=0;
        mm=me[can[0]];
        f=can[0];
        bool tieflag=false;
        int mf;
        for(int j=1;j<can.size();j++)
        {
            if(mm<con_e[can[j]])
            {
                mm=con_e[can[j]];
                f=can[j];
                pos=j;
                tieflag=false;
                mf=me[can[j]];
            }
            else if(mm==con_e[can[j]])
            {
                tieflag=true;
            }
        }
        if(!tieflag)
        mt[order++]=f;
        else
        {
            for(int j=0;j<can.size();j++)
            {
                if(mm==con_e[can[j]])
                {
                    if(mf>me[can[j]])
                    {
                        mf=me[can[j]];
                        f=can[j];
                        pos=j;
                    }
                }
            }
            mt[order++]=f;
        }
        tm[f]=order-1;
        neibor[f]=neibor_can[f];
        can.erase(can.begin()+pos);
        enq[f].flag=true;
        int ad=0;
        for(int j=0;j<enq[f].adj.size();j++)
        {
            enq[enq[f].adj[j]].flag2=true;
            if(enq[enq[f].adj[j]].flag2&&!enq[enq[f].adj[j]].flag)
            {
                can.push_back(enq[f].adj[j]);
                ad++;
            }
            neibor_can[enq[f].adj[j]]=order-1;
        }
        kk+=ad;
    }
}
void matchorder()
{//forest有eq_num-temp个，需要join操作eq_num-temp-1次
    for(int i=1;i<=eq_num;i++)
    {
        int iqs=atoi(eq[i].source_id.c_str());
        int iqt=atoi(eq[i].target_id.c_str());
        for(int j=0;j<vec[i].size();j++)
        {
            int isn=atoi(eg[vec[i][j]].source_id.c_str());
            int itn=atoi(eg[vec[i][j]].target_id.c_str());
            if(vg[isn].indegree<vq[iqs].indegree||vg[itn].outdegree<vq[iqt].outdegree||vg[isn].outdegree<vq[iqs].outdegree||vg[itn].indegree<vq[iqt].indegree)
            {
                vec[i].erase(vec[i].begin()+j);
                me[i]--;
                j--;
                continue;
            }
            bool flage=true;
            for(int k=0;k<vq[iqs].adj1.size();k++)
            {
                bool flage1=false;
                for(int l=0;l<vg[isn].adj1.size();l++)
                {
                    if(lg[to_string(vg[isn].adj1[l])]==lq[to_string(vq[iqs].adj1[k])])
                    {
                        flage1=true;
                        break;
                    }
                }
                if(!flage1)
                {
                    flage=false;
                    vec[i].erase(vec[i].begin()+j);
                    me[i]--;
                    j--;
                    break;
                }
            }
            if(!flage)
            continue;
            for(int k=0;k<vq[iqs].adj2.size();k++)
            {
                bool flage1=false;
                for(int l=0;l<vg[isn].adj2.size();l++)
                {
                    if(lg[to_string(vg[isn].adj2[l])]==lq[to_string(vq[iqs].adj2[k])])
                    {
                        flage1=true;
                        break;
                    }
                }
                if(!flage1)
                {
                    flage=false;
                    vec[i].erase(vec[i].begin()+j);
                    me[i]--;
                    j--;
                    break;
                }
            }
            if(!flage)
            continue;
            for(int k=0;k<vq[iqt].adj1.size();k++)
            {
                bool flage1=false;
                for(int l=0;l<vg[itn].adj1.size();l++)
                {
                    if(lg[to_string(vg[itn].adj1[l])]==lq[to_string(vq[iqt].adj1[k])])
                    {
                        flage1=true;
                        break;
                    }
                }
                if(!flage1)
                {
                    flage=false;
                    vec[i].erase(vec[i].begin()+j);
                    me[i]--;
                    j--;
                    break;
                }
            }
            if(!flage)
            continue;
            for(int k=0;k<vq[iqt].adj2.size();k++)
            {
                bool flage1=false;
                for(int l=0;l<vg[itn].adj2.size();l++)
                {
                    if(lg[to_string(vg[itn].adj2[l])]==lq[to_string(vq[iqt].adj2[k])])
                    {
                        flage1=true;
                        break;
                    }
                }
                if(!flage1)
                {
                    flage=false;
                    vec[i].erase(vec[i].begin()+j);
                    me[i]--;
                    j--;
                    break;
                }
            }
        }
    }
    mm=con_e[1];
    int k=eq_num-temp+1;
    while(k--)
    {
        cluster_join();
        cluster_order();
    }
    for(int j=1;j<=arrc;j++)
    {
        int count=0;
        for(int k=1;k<=eq_num;k++)
        {
            if(mt[k]==arr[j][1]||mt[k]==arr[j][2])
            count++;
            if(count==2)
            {
                arr[j][4]=k;
                break;
            }
        }
    }
    mtemp=1;
    int iqs=atoi(eq[mt[1]].source_id.c_str());
    int iqt=atoi(eq[mt[1]].target_id.c_str());
    mtv[mtemp++]=iqs;
    tmv[iqs]=mtemp-1;
    vbf[iqs]=1;
    mtv[mtemp++]=iqt;
    tmv[iqt]=mtemp-1;
    vbf[iqt]=1;
    for(int i=2;i<=eq_num;i++)
    {
        int iqs=atoi(eq[mt[i]].source_id.c_str());
        int iqt=atoi(eq[mt[i]].target_id.c_str());
        int diraj=neibor[mt[i]];
        int join;
        string emode=eq_mode(mt[diraj],mt[i],join);
        if(emode[0]=='1')
        {
            if(iqs==join)
            {
                if(vbf[iqt]!=1)
                {
                    mtv[mtemp++]=iqt;
                    tmv[iqt]=mtemp-1;
                    vbf[iqt]=1;
                }
            }
            else
            {
                if(vbf[iqs]!=1)
                {
                    mtv[mtemp++]=iqs;
                    tmv[iqs]=mtemp-1;
                    vbf[iqs]=1;
                }
            }
        }
    }
}
bool vmatch(int vvg,int ord)
{
    for(int k=0;k<vq[mtv[ord]].adj1.size();k++)
    {
        if(tmv[vq[mtv[ord]].adj1[k]]<ord)
        {
            bool vflag1=false;
            for(int l=0;l<vg[vvg].adj1.size();l++)
            {
                if(matchv[tmv[vq[mtv[ord]].adj1[k]]]==vg[vvg].adj1[l])
                {
                    vflag1=true;
                    break;
                }
            }
            if(!vflag1)
            return false;
        }
        else
        {
            bool vflag=false;
            for(int l=0;l<vg[vvg].adj1.size();l++)
            {
                if(lg[to_string(vg[vvg].adj1[l])]==lq[to_string(vq[mtv[ord]].adj1[k])]&&vg[vg[vvg].adj1[l]].indegree>=vq[vq[mtv[ord]].adj1[k]].indegree&&vg[vg[vvg].adj1[l]].outdegree>=vq[vq[mtv[ord]].adj1[k]].outdegree)
                {
                    vflag=true;
                    break;
                }
            }
            if(!vflag)
            return false;
        }
    }
    for(int k=0;k<vq[mtv[ord]].adj2.size();k++)
    {//判断与已经匹配的顶点是否能匹配上
        if(tmv[vq[mtv[ord]].adj2[k]]<ord)
        {
            bool vflag1=false;
            for(int l=0;l<vg[vvg].adj2.size();l++)
            {
                int di=matchv[tmv[vq[mtv[ord]].adj2[k]]];
                if(matchv[tmv[vq[mtv[ord]].adj2[k]]]==vg[vvg].adj2[l])
                {                                
                    vflag1=true;
                    break;
                }
            }
            if(!vflag1)
            return false;
        }
        else
        {
            bool vflag=false;
            for(int l=0;l<vg[vvg].adj2.size();l++)
            {
                if(lg[to_string(vg[vvg].adj2[l])]==lq[to_string(vq[mtv[ord]].adj2[k])]&&vg[vg[vvg].adj2[l]].indegree>=vq[vq[mtv[ord]].adj2[k]].indegree&&vg[vg[vvg].adj2[l]].outdegree>=vq[vq[mtv[ord]].adj2[k]].outdegree)
                {
                    vflag=true;
                    break;
                }
            }
            if(!vflag)
            return false;
        }
    }
    return true;
}
void expandmatching(int dep,int mavd)
{
    if(dep==eq_num+1)//已经形成一个匹配结果
    {
        match_num++;
        cout<<match_num<<":";
        for(int j=1;j<=eq_num;j++)
        cout<<matche[j]<<" ";
        cout<<endl;
        for(int j=1;j<=eq_num;j++)
        cout<<eg[matche[j]].source_id<<"-->"<<eg[matche[j]].target_id<<" ";
        cout<<endl;
        for(int j=1;j<=vq_num;j++)
        cout<<matchv[j]<<" ";
        cout<<endl;
    }
    else
    {
        int diradj=neibor[mt[dep]];//第n条匹配边的直接邻居,mt[n]是第n条匹配边在query中的编号
        int vjoin;
        string emode=eq_mode(mt[diradj],mt[dep],vjoin);
        int isq=atoi(eq[mt[dep]].source_id.c_str());
        int itq=atoi(eq[mt[dep]].target_id.c_str());
        int isn=atoi(eg[matche[diradj]].source_id.c_str()); 
        int itn=atoi(eg[matche[diradj]].target_id.c_str());
        if(emode[0]=='2')//两边是同一对顶点之间的
        {
            if(emode[1]=='1')//共同顶点是目标结点
            {
                int jointemp=atoi(eg[matche[diradj]].target_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                int anot=atoi(eg[matche[diradj]].source_id.c_str());//另一共同顶点（源结点）
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj])
                        {
                            matche[dep]=vg[jointemp].adje2[j];//vttg
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]])
                        {
                            matche[dep]=vg[jointemp].adje2[j];//vttg
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]])
                        {
                            matche[dep]=vg[jointemp].adje2[j];//vttg
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
            }
            else if(emode[1]=='2')//共同顶点是源结点
            {
                int jointemp=atoi(eg[matche[diradj]].source_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                int anot=atoi(eg[matche[diradj]].target_id.c_str());//另一共同顶点（源结点）
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
            }
            else if(emode[1]=='3')//邻居的目标结点是匹配边的源结点
            {
                int jointemp=atoi(eg[matche[diradj]].target_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                int anot=atoi(eg[matche[diradj]].source_id.c_str());//另一共同顶点（源结点）
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(vg[jointemp].adj1[j]==anot&&vg[jointemp].adje1[j]!=matche[diradj]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]])
                        {
                            matche[dep]=vg[jointemp].adje1[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
            }
            else//邻居的源结点是该匹配的目标结点
            {
                int jointemp=atoi(eg[matche[diradj]].source_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                int anot=atoi(eg[matche[diradj]].target_id.c_str());//另一共同顶点（源结点）
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj])
                        {
                            matche[dep]=vg[jointemp].adje2[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]])
                        {
                            matche[dep]=vg[jointemp].adje2[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(vg[jointemp].adj2[j]==anot&&vg[jointemp].adje2[j]!=matche[diradj]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]])
                        {
                            matche[dep]=vg[jointemp].adje2[j];
                            bool tflag=true;
                            for(int l=1;l<=arrc;l++)
                            {
                                if(arr[l][4]==dep)
                                {
                                    bool tflag1=false;
                                    //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                    if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1,mavd);
                        }
                    }
                }
            }
        }
        else//两边只共用一个顶点
        {
            if(emode[1]=='1')//两边共用邻居结点的目标结点
            {
                int jointemp=atoi(eg[matche[diradj]].target_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                { 
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        //if(eg[match[tm[arr[l][2]]]].dur>eg[match[tm[arr[l][1]]]].dur)
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            else if(emode[1]=='2')//共同顶点是源结点
            {
                int jointemp=atoi(eg[matche[diradj]].source_id.c_str());//共同顶点（源结点）如果没有边，有共同顶点也是不成立的
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&vg[vg[isn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[jointemp].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[isn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            else if(emode[1]=='3')//邻居的目标结点是匹配边的源结点
            {
                int jointemp=atoi(eg[matche[diradj]].target_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&vg[vg[jointemp].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[itn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                         break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj1[j])]==lq[eq[mt[dep]].target_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[itn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(tmv[itq]<mavd&&matchv[tmv[itq]]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj1[l])]==lq[to_string(vq[itq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[itq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[itn].adj1[j]].adj2[l])]==lq[to_string(vq[itq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[itq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj1[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj1[j]; 
                                            vbf[itq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[itq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            else//邻居的源结点是该匹配的目标结点
            {
                int jointemp=atoi(eg[matche[diradj]].source_id.c_str());//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                if(emode[2]=='3')//两边之间没有时间限制
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else//邻居是大边
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[to_string(vg[jointemp].adj2[j])]==lq[eq[mt[dep]].source_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(tmv[isq]<mavd&&matchv[tmv[isq]]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj1[l])]==lq[to_string(vq[isq].adj1[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(!flage)
                            continue;
                            for(int k=0;k<vq[isq].adj2.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj2.size();l++)
                                {
                                    if(lg[to_string(vg[vg[isn].adj2[j]].adj2[l])]==lq[to_string(vq[isq].adj2[k])])
                                    {
                                        flage1=true;
                                        break;
                                    }
                                }
                                if(!flage1)
                                {
                                    flage=false;
                                    break;
                                }
                            }
                            if(flage)
                            {
                                matche[dep]=vg[jointemp].adje2[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tm[arr[l][2]]]].dur>eg[matche[tm[arr[l][1]]]].dur&&(eg[matche[tm[arr[l][2]]]].dur-eg[matche[tm[arr[l][1]]]].dur)<=arr[l][3])
                                        tflag1=true;
                                        if(!tflag1)
                                        {
                                            tflag=false;
                                            break;
                                        }
                                    }
                                }
                                if(tflag)
                                {//点匹配
                                    if(vbf[isq]==2)
                                    expandmatching(dep+1,mavd);
                                    else
                                    {
                                        if(vmatch(vg[jointemp].adj2[j],mavd))
                                        {
                                            matchv[mavd]=vg[jointemp].adj2[j]; 
                                            vbf[isq]=2;
                                            expandmatching(dep+1,mavd+1);
                                            vbf[isq]=1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
void pamt()
{
    //边两边的标签已经匹配上了，语义符合,出入度也符合  匹配每一条边
    for(int k=0;k<vec[mt[1]].size();k++)//匹配matchorder中的第一条边
    {
        ma=1;
        mav=1;
        matche[ma++]=vec[mt[1]][k];
        int isn=atoi(eg[vec[mt[1]][k]].source_id.c_str());
        int itn=atoi(eg[vec[mt[1]][k]].target_id.c_str());
        int iqs=atoi(eq[mt[1]].source_id.c_str());
        int iqt=atoi(eq[mt[1]].target_id.c_str());
        matchv[mav++]=isn;
        vbf[iqs]=2;
        bool vflag=true;//vt=itn//点匹配
        for(int k=0;k<vq[mtv[2]].adj1.size();k++)
        {
            if(tmv[vq[mtv[2]].adj1[k]]<2)
            {
                bool vflag1=false;
                for(int l=0;l<vg[itn].adj1.size();l++)
                {
                    if(matchv[tmv[vq[mtv[2]].adj1[k]]]==vg[itn].adj1[l])
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
        for(int k=0;k<vq[mtv[2]].adj2.size();k++)
        {//判断与已经匹配的顶点是否能匹配上
            if(tmv[vq[mtv[2]].adj2[k]]<2)
            {
                bool vflag1=false;
                for(int l=0;l<vg[itn].adj2.size();l++)
                {
                    if(matchv[tmv[vq[mtv[2]].adj2[k]]]==vg[itn].adj2[l])
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
        if(vflag)
        {
            //int mavd=3;
            matchv[mav++]=itn; 
            vbf[iqt]=2;
            expandmatching(ma,mav);//ma=2,mavd=3
        }
    }
}
int main()
{
    clock_t start_time, end_time;
    
    readquery();//读query
    for(int j=0;j<=vq_num;j++)
    {
        string str=to_string(j);
        cout<<lq[str]<<endl;
    }
    creatforest();//构造query森林
    cout<<"creatforest successful!"<<endl;
    cout<<"temp:"<<temp<<endl;
    for(int j=1;j<temp;j++)
    {
        cout<<j<<":"<<eeq[j].from<<" "<<eeq[j].to<<endl;
    }
    readedgelista();//读账户信息数据
    readedgelistaa();//读账户间转账数据
    start_time = clock();
    matchorder();
    cout<<"matchorder:";
    for(int j=1;j<=eq_num;j++)
    cout<<mt[j]<<" ";
    cout<<endl;
    for(int j=1;j<=vq_num;j++)
    cout<<mtv[j]<<" ";
    cout<<endl;
    pamt();
    end_time = clock();     //获取结束时间
    double Times = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    cout<<Times<<"seconds"<<endl;
    return 0;

}
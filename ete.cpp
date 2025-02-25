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
int sum(int year,int month,int day)//与2001年1月1日相差几天Calculate the number of days since January 1, 2001
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
    vector<int> adj1;//出边邻居结点Outgoing neighboring vertexs
    vector<int> adje1;
    vector<int> adj2;//入边邻居结点Incoming neighboring vertexs
    vector<int> adje2;
};
struct vquery//vq[20]
{
    int indegree,outdegree;
    vector<int> adj1;//邻居结点,出边Outgoing neighboring vertexs
    // Adjacent edges, one-to-one correspondence with each position in adj, can determine which edge corresponds to the neighbor node
    vector<int> adje1;//邻接边，与adj的每一位置一一对应，可以从邻居结点对应上是哪条边
    vector<int> adj2;//邻居结点//Incoming neighboring vertexs
    vector<int> adje2;
};
struct edge//eg[maxn]
{
    int source_id;// 边的起始顶点号，事务的发起方// The starting vertex ID of the edge, the initiator of the transaction
    int target_id;//边的终结顶点号，事务的结束方// The ending vertex ID of the edge, the terminator of the transaction
    int dur;//时间发生的日期与2020/1/1的距离// The distance of the date when the event occurs from 2020/1/1
};
struct equery//eq[20]
{
    int source_id;
    int target_id;
};
struct edgenode//enq[20],边结点，enq与eq是一一对应的// Edge nodes, enq and eq are one-to-one correspondence
{
    int id;
    vector<int> adj;
    vector<int> adje;
    int indegree,outdegree;
    bool flag;//判断是否已在matchorder中// Check if it is already in matchorder
    bool flag2;//判断是否是matchorder中某一边结点的邻结点// Check if it is a neighboring node of any edge node in matchorder
};

struct edgever
{
    int id;
    int degree;
    vector<int> adj;
    bool flage;
};

int temp=1;//判断是否把所有边结点加入生成树的全局变量// Global variable to check if all vertices have been added to matchorder
int ma=1;//指示当前在匹配哪条边，matchorder中的次序// Indicates which edge is currently being matched, the order in matchorder
int match_num=0;//记录有多少个匹配// Record the number of matches
int eq_num=0,vq_num=0,label_num=0;//query边数量，结点数量，标签种类// Number of query edges, number of nodes, number of label types
int v_num,e_num;////分别代表顶点数目和边数目,// Represent the number of vertices and edges, respectively
int order=1;
int f=1,mm;
edge eg[maxn];//
vertex vg[maxn];
equery eq[20];//query的边集// Edge set of the query
vquery vq[20];//query的点集// Vertex set of the query
edgenode enq[20];//query中的边转化为结点// Convert edges in the query to nodes
int me[20];//query相应边与待查询图中边的匹配数量// The number of matches between the corresponding edges of the query and the edges in the graph to be queried
//int me[8]={0,10088,16788,19013,8114,25126,7030,6842};
int mt[20];//边的匹配顺序The matching order of edges
int tmm[20];//由order反求边// The matching order of the intermediate points of the edges
int timeconstrain[20][20];
int con_e[20];//记录每条边出现在时间限制组合中的次数// Record the number of times each edge appears in the temporal constraint combinations
int matche[20];//边匹配结果// Edge matching result
int matchv[20];//中间顶点匹配结果// Matching result of the intermediate vertices
int neibor[20];//形成matchorder的直接邻居// Direct neighbors forming the matchorder
int neibor_can[20];//形成matchorder的候选邻居// Candidate neighbors forming the matchorder
int neiborsp_can[20];//直接邻居种类的候选/ Candidate types of direct neighbors
map<int,string>lg;//账户对应的类型// Type corresponding to the account
map<int,string>lq;//query的顶点标签// Vertex label of the query
string label[20];//query顶点的标签// Vertex label of the query
int arrc;
int che[20];
map<int,int> vv;
// Store each combination: 
// arr[i][1] is the first vertex of the combination, 
// arr[i][2] is the second vertex of the combination, 
// arr[i][3] is the third vertex of the combination, 
// arr[i][4] is the minimum position where all vertices in the combination appear in the order
int arr[20][6];//存储每一个组合，arr[i][1]为组合的第一条边,arr[i][2]为组合的第二,arr[i][3]为组中两条边的时间限制大小,arr[i][4]为组合中所有顶点都在order中出现的最小位置
vector< vector<int> > vec(20);//存储候选匹配边结点
string unixstamp_to_data(time_t unix_timestamp)
{
    // 将 Unix 时间戳转换为时间点// Convert Unix timestamp to a point in time
    chrono::system_clock::time_point time_point =std::chrono::system_clock::from_time_t(unix_timestamp);
    // 将时间点转换为本地时间// Convert the time point to local time
    time_t local_time = std::chrono::system_clock::to_time_t(time_point);
    // 将本地时间转换为可读的日期时间字符串// Convert local time to a readable date-time string
    stringstream ss;
    ss << std::put_time(std::localtime(&local_time), "%Y-%m-%d %H:%M:%S");
    string datetime_str=ss.str();
    return datetime_str;

}
string eq_mode(int e1,int e2,int &n)
{
    if(eq[e1].target_id==eq[e2].target_id)//共用一个目标结点// Share a common target node
    {
        n=eq[e1].target_id;
        if(eq[e1].source_id==eq[e2].source_id)//并且共用一个源结点，两个顶点之间同向的两条边// Also share a common source node, two vertices with two edges in the same direction
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
    if(eq[e1].source_id==eq[e2].source_id)//共用一个源结点//Share a common source node
    {
        n=eq[e1].source_id;
        // Share a common target node, two vertices with two edges in the same direction
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
    if(eq[e1].target_id==eq[e2].source_id)//e1的目标结点是e2的源结点//The target node of e1 is the source node of e2
    {
        n=eq[e1].target_id;
        // The target node of e2 is the source node of e1, two vertices with two edges in opposite directions
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
    if(eq[e1].source_id==eq[e2].target_id)//e1的源结点是e2的目标结点// The source node of e1 is the target node of e2
    {
        n=eq[e2].target_id;
        // The target node of e1 is the source node of e2, two vertices with two edges in opposite directions
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

void readquery()//读查询图的边，顶点标签，边的时序// Read the edges, vertex labels, and temporal order of the query graph
{
    ifstream rd("query/q3tc3.txt");
    if(!rd)
    {
        cout<<"error!"<<endl;
        exit(1);
    }
    cout<<"read query11 successful!"<<endl;
    string a,b;
    int i=1,j=0,k=0,etci=1,cou=1;//i是边序号// i is the edge index
    while(rd>>a>>b)//读每一条边，源结点和终结点// Read each edge, including the source node and the target node
    {
        cout<<a<<" "<<b<<endl;
        if(a=="|")
        break;
        int ia=atoi(a.c_str());
        int ib=atoi(b.c_str());
        eq[i].source_id=ia;
        eq[i].target_id=ib;
        enq[i].id=i;
        enq[i].flag=false;
        enq[i].flag2=false;
        
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
        i++;
    }
    string c,d;
    while(rd>>c>>d)//读每个顶点的标签// Read the label of each vertex
    {
        cout<<c<<" "<<d<<endl;
        if(c=="|")
        break;
        int ic=atoi(c.c_str());
        lq[ic]=d;
        label[j++]=d;
    }
    string e,f;
    int g;
    for(int k=0;k<i;k++)
    con_e[k]=0;
    while(rd>>e>>f>>g)//读每一组时间限制// Read each set of time constraints
    {
        cout<<e<<" "<<f<<" "<<g<<endl;
        int ia=atoi(e.c_str());
        int ib=atoi(f.c_str());
        con_e[ia]++;
        con_e[ib]++;
        timeconstrain[ia][ib]=g;
        timeconstrain[ib][ia]=-g;
        int ss=eq[ia].source_id;
        int st=eq[ia].target_id;
        int ls=eq[ib].source_id;
        int lt=eq[ib].target_id;
        arr[cou][1]=ia;
        arr[cou][2]=ib;
        arr[cou][3]=g;
        cou++;
        
        
    }
    eq_num=i-1;
    vq_num=k;
    label_num=j-1;
    arrc=cou-1;
    rd.close();
}
void creatforest()
{
    for(int i=1;i<=vq_num;i++)//遍历所有顶点// Traverse all vertices
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
                    enq[ve[j]].outdegree++;
                    enq[ve[k]].indegree++;
                    enq[ve[j]].adj.push_back(ve[k]);
                    enq[ve[j]].adje.push_back(temp);
                    enq[ve[k]].adj.push_back(ve[j]);
                    enq[ve[k]].adje.push_back(temp);
                    temp++;
                    //判断是否有环// Check if there is a cycle
                    edgever entq[eq_num+1];
                    for(int kk=1;kk<=eq_num;kk++)
                    {
                        entq[kk].flage=true;
                        entq[kk].id=enq[kk].id;
                        entq[kk].degree=enq[kk].indegree+enq[kk].outdegree;
                        entq[kk].adj.insert(entq[kk].adj.end(),enq[kk].adj.begin(),enq[kk].adj.end());
                    }
                    int del=0;//记录删除了几个顶点// Record the number of vertices deleted
                    int coun=0;//记录度<=1的顶点个数// Record the number of vertices with degree <= 1
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
                                entq[l].flage=false;//删除了顶点l// Vertex l has been deleted
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
                    if(del<eq_num)//如果加入这条边成环了，则不加入这条边// If adding this edge forms a cycle, then do not add this edge
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
void readedgelista()
{
    //ifstream rda("dataset/label_8.txt");
    //ifstream rda("dataset/college_msg_label.txt");
    //ifstream rda("dataset/email_eu_label.txt");
    //ifstream rda("dataset/stackoverflow_label.txt");
    //ifstream rda("dataset/mathoverflow_label.txt");
    //ifstream rda("dataset/ubuntu_label.txt");
    //ifstream rda("dataset/superuser_label.txt");
    ifstream rda("dataset/wiki_talk_label.txt");
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
            int vi=atoi(ver.c_str());
            if(lab==label[i])
            {
                lg[vi]=lab;
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
    //ifstream rdaa("dataset/stackoverflow.txt");
    //ifstream rdaa("dataset/mathoverflow.txt");
    //ifstream rdaa("dataset/ubuntu.txt");
    //ifstream rdaa("dataset/superuser.txt");
    //ifstream rdaa("dataset/college_msg.txt");
    ifstream rdaa("dataset/wiki_talk.txt");
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
        int si=atoi(sn.c_str());
        int ti=atoi(tn.c_str());
        //if(s%5!=1)
        //continue;
        if(lg.count(si)==0||lg.count(ti)==0)
        continue;
        else
        {
            eg[i].source_id=si;
            eg[i].target_id=ti;
            int u2=atoi(tsu.c_str());
            time_t un=(time_t)u2;
            ts=unixstamp_to_data(un);
            string ye=ts.substr(0,4),mo=ts.substr(5,2),da=ts.substr(8,2);
            int year=atoi(ye.c_str()),mon=atoi(mo.c_str()),day=atoi(da.c_str());
            eg[i].dur=sum(year,mon,day);
            for(int j=1;j<=eq_num;j++)
            {
                if(lg[si]==lq[eq[j].source_id]&&lg[ti]==lq[eq[j].target_id])
                {
                    me[j]++;
                    vec[j].push_back(i);
                }
            }
            
            if(k<si)
            k=si;
            if(k<ti)
            k=ti;
            vg[si].outdegree++;
            vg[ti].indegree++;
            vg[si].adj1.push_back(ti);
            vg[si].adje1.push_back(i);
            vg[ti].adj2.push_back(si);
            vg[ti].adje2.push_back(i);
            i++;
        }
    }  
    e_num=i-1;//75463
    v_num=k;
    cout<<"read graph g successful!"<<endl;
    rdaa.close();
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
        mt[order++]=f;//第一条匹配的边// The first matched edge
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
        tmm[f]=order-1;
        enq[f].flag=true;
        enq[f].flag2=true;
    }
    else
    {
        vector<int> can;//即将加入matchorder的候选边结点// The candidate edge node to be added to matchorder
        for(int j=1;j<order;j++)
        {
            int isn=eq[mt[j]].source_id;
            int itn=eq[mt[j]].target_id;
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
        tmm[f]=order-1;
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
        neibor_can[enq[f].adj[j]]=order-1;//邻居结点直接是matchorder中的顺序// The order of the neighbor nodes directly in matchorder
    }
    int kk=enq[f].adj.size();
    while(kk--)
    {
        int pos=0;
        mm=con_e[can[0]];
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
        tmm[f]=order-1;
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
{//forest有eq_num-temp个，需要join操作eq_num-temp-1次// There are eq_num - temp forests, requiring eq_num - temp - 1 join operations
    for(int i=1;i<=eq_num;i++)
    {
        int iqs=eq[i].source_id;
        int iqt=eq[i].target_id;
        for(int j=0;j<vec[i].size();j++)
        {
            int isn=eg[vec[i][j]].source_id;
            int itn=eg[vec[i][j]].target_id;
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
                    if(lg[vg[isn].adj1[l]]==lq[vq[iqs].adj1[k]])
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
                    if(lg[vg[isn].adj2[l]]==lq[vq[iqs].adj2[k]])
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
                    if(lg[vg[itn].adj1[l]]==lq[vq[iqt].adj1[k]])
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
                    if(lg[vg[itn].adj2[l]]==lq[vq[iqt].adj2[k]])
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
}
void expandmatching(int dep)
{
    if(dep==eq_num+1)//已经形成一个匹配结果// A matching result has been formed
    {
        match_num++;
        cout<<match_num<<":";
        cout<<matche[1]<<" ";
        for(int j=2;j<=eq_num;j++)
        cout<<matchv[j]<<" "<<matche[j]<<" ";
        cout<<endl;
        for(int j=1;j<=eq_num;j++)
        cout<<eg[matche[j]].source_id<<"-->"<<eg[matche[j]].target_id<<" ";
        cout<<endl;
    }
    else
    {
        vec[mt[dep]].clear();
        // Direct neighbors of the nth matched edge, mt[n] is the index of the nth matched edge in the query
        int diradj=neibor[mt[dep]];//第n条匹配边的直接邻居,mt[n]是第n条匹配边在query中的编号
        int vjoin;
        string emode=eq_mode(mt[diradj],mt[dep],vjoin);
        int isq=eq[mt[dep]].source_id;
        int itq=eq[mt[dep]].target_id;
        int isn=eg[matche[diradj]].source_id; 
        int itn=eg[matche[diradj]].target_id;
        if(emode[0]=='2')//两边是同一对顶点之间的// The two edges are between the same pair of vertices
        {
            if(emode[1]=='1')//共同顶点是目标结点// The common vertex is the target node
            {
                // If the common vertex (target node) has no edge, having a common vertex is also invalid
                int jointemp=eg[matche[diradj]].target_id;//共同顶点（目标结点）如果没有边，有共同顶点也是不成立的
                int anot=eg[matche[diradj]].source_id;//另一共同顶点（源结点）// The other common vertex (source node)
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
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
                                //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
            }
            else if(emode[1]=='2')//共同顶点是源结点// The common vertex is the source node
            {
                int jointemp=eg[matche[diradj]].source_id;
                int anot=eg[matche[diradj]].target_id;//另一共同顶点（源结点）//另一共同顶点（源结点）// The other common vertex (source node)
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                        tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
            }
            else if(emode[1]=='3')//邻居的目标结点是匹配边的源结点// The target node of the neighbor is the source node of the matched edge
            {
                int jointemp=eg[matche[diradj]].target_id;
                int anot=eg[matche[diradj]].source_id;//另一共同顶点（源结点）// The other common vertex (source node)
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
            }
            else//邻居的源结点是该匹配的目标结点// The source node of the neighbor is the target node of the matched edge
            {
                int jointemp=eg[matche[diradj]].source_id;
                int anot=eg[matche[diradj]].target_id;//另一共同顶点（源结点）// The other common vertex (source node)
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
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
                                    //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                    if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
                                    tflag1=true;
                                    if(!tflag1)
                                    {
                                       tflag=false;
                                        break;
                                    }
                                }
                            }
                            if(tflag)
                            expandmatching(dep+1);
                        }
                    }
                }
            }
        }
        else//两边只共用一个顶点// The two edges share only one vertex
        {
            if(emode[1]=='1')//两边共用邻居结点的目标结点// The two edges share the target node of the neighbor
            {
                int jointemp=eg[matche[diradj]].target_id;
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        //if(eg[match[tmm[arr[l][2]]]].dur>eg[match[tmm[arr[l][1]]]].dur)
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[itn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[itn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
                                }
                            }
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[jointemp].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[itn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[itn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
                                }
                            }
                        }
                    }
                }
            }
            else if(emode[1]=='2')//共同顶点是源结点// The common vertex is the source node
            {
                int jointemp=eg[matche[diradj]].source_id;
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&vg[vg[isn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                 matchv[dep]=jointemp;
                                 matche[dep]=vg[jointemp].adje1[j];
                                 bool tflag=true;
                                 for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[isn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[isn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[isn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[isn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[isn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[isn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
            }
            else if(emode[1]=='3')//邻居的目标结点是匹配边的源结点// The target node of the neighbor is the source node of the matched edge
            {
                int jointemp=eg[matche[diradj]].target_id;
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&vg[vg[jointemp].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[itn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&eg[vg[jointemp].adje1[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje1[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[itn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                matchv[dep]=jointemp;
                                matche[dep]=vg[jointemp].adje1[j];
                                bool tflag=true;
                                for(int l=1;l<=arrc;l++)
                                {
                                    if(arr[l][4]==dep)
                                    {
                                        bool tflag1=false;
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[itn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
                {
                    for(int j=0;j<vg[jointemp].adje1.size();j++)
                    {
                        if(lg[vg[jointemp].adj1[j]]==lq[eq[mt[dep]].target_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje1[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje1[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[itn].adj1[j]].indegree>=vq[itq].indegree)
                        {
                            if(che[itq]!=0&&vv[itq]!=vg[itn].adj1[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[itq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[itn].adj1[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[itn].adj1[j]].adj1[l]]==lq[vq[itq].adj1[k]])
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
                                    if(lg[vg[vg[itn].adj1[j]].adj2[l]]==lq[vq[itq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[itq]==0)
                                    vv[itq]=vg[itn].adj1[j];
                                    che[itq]++;
                                    expandmatching(dep+1);
                                    che[itq]--;
                                }
                            }
                        }
                    }
                }
            }
            else//邻居的源结点是该匹配的目标结点// The source node of the neighbor is the target node of the matched edge
            {
                int jointemp=eg[matche[diradj]].source_id;
                if(emode[2]=='3')//两边之间没有时间限制// There is no time constraint between the two edges
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[isn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
                                }
                            }
                        }
                    }
                }
                else if(emode[2]=='1')//邻居是小边// The neighbor is a minor edge
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&eg[vg[jointemp].adje2[j]].dur>eg[matche[diradj]].dur&&(eg[vg[jointemp].adje2[j]].dur-eg[matche[diradj]].dur)<=timeconstrain[mt[diradj]][mt[dep]]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[isn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
                                }
                            }
                        }
                    }
                }
                else//邻居是大边// The neighbor is a major edge
                {
                    for(int j=0;j<vg[jointemp].adje2.size();j++)
                    {
                        if(lg[vg[jointemp].adj2[j]]==lq[eq[mt[dep]].source_id]&&eg[matche[diradj]].dur>eg[vg[jointemp].adje2[j]].dur&&(eg[matche[diradj]].dur-eg[vg[jointemp].adje2[j]].dur)<=timeconstrain[mt[dep]][mt[diradj]]&&vg[vg[isn].adj2[j]].outdegree>=vq[isq].outdegree)
                        {
                            if(che[isq]!=0&&vv[isq]!=vg[isn].adj2[j])
                            continue;
                            bool flage=true;
                            for(int k=0;k<vq[isq].adj1.size();k++)
                            {
                                bool flage1=false;
                                for(int l=0;l<vg[vg[isn].adj2[j]].adj1.size();l++)
                                {
                                    if(lg[vg[vg[isn].adj2[j]].adj1[l]]==lq[vq[isq].adj1[k]])
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
                                    if(lg[vg[vg[isn].adj2[j]].adj2[l]]==lq[vq[isq].adj2[k]])
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
                                        if(eg[matche[tmm[arr[l][2]]]].dur>eg[matche[tmm[arr[l][1]]]].dur&&(eg[matche[tmm[arr[l][2]]]].dur-eg[matche[tmm[arr[l][1]]]].dur)<=arr[l][3])
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
                                    if(che[isq]==0)
                                    vv[isq]=vg[isn].adj2[j];
                                    che[isq]++;
                                    expandmatching(dep+1);
                                    che[isq]--;
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
    // The labels on both sides of the edge have been matched, the semantics are consistent, and the in-degree and out-degree are also consistent. Match each edge.
    for(int k=0;k<vec[mt[1]].size();k++)//匹配matchorder中的第一条边// Match the first edge in matchorder
    {
        ma=1;
        for(int i=1;i<=eq_num;i++)
        che[i]=0;
        matche[ma++]=vec[mt[1]][k];
        int isn=eg[vec[mt[1]][k]].source_id;
        int itn=eg[vec[mt[1]][k]].target_id;
        int iqs=eq[mt[1]].source_id;
        int iqt=eq[mt[1]].target_id;
        che[iqs]++;
        che[iqt]++;
        vv[iqs]=isn;
        vv[iqt]=itn;
        expandmatching(ma);
    }
}
int main()
{
    clock_t start_time,process_time,end_time;
    
    readquery();//读query//Read the query
    creatforest();//构造query森林// Construct the query forest
    cout<<"creatforest successful!"<<endl;
    cout<<"temp:"<<temp<<endl;

    readedgelista();//读账户信息数据// Read the account information data
    readedgelistaa();//读账户间转账数据// Read the account transfer data
    start_time = clock();
    matchorder();
    cout<<"matchorder:";
    for(int j=1;j<=eq_num;j++)
    cout<<mt[j]<<" ";
    cout<<endl;
    process_time=clock();
    pamt();
    end_time = clock();     //获取结束时间// Get the end time
    double Times1 = (double)(process_time - start_time) / CLOCKS_PER_SEC;
    cout<<"process time:"<<Times1<<"seconds"<<endl;
    double Times2 = (double)(end_time - process_time) / CLOCKS_PER_SEC;
    cout<<"matching time:"<<Times2<<"seconds"<<endl;
    double Times = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    cout<<"total time:"<<Times<<"seconds"<<endl;
    //double Times = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    //cout<<Times<<"seconds"<<endl;
    return 0;

}


Index of Contents:

 1. Cut Edge ----------------------------------------------------------- 3
 2. Cut Vertex --------------------------------------------------------- 3
 3. Eulerian Tour ------------------------------------------------------ 4
 4. Big Num ------------------------------------------------------------ 5
 5. Linear Equation Solver --------------------------------------------- 8
 6. Matrix Inversion --------------------------------------------------- 10
 7. Polygon Similarity ------------------------------------------------- 12
 8. Weighted Matching -------------------------------------------------- 14
 9. Stoer-Wagner MinCut ------------------------------------------------ 15
10. Max Bipartite Matching and Min Vertex Cover ------------------------ 16
11. Maximum Flow (Ford-Fulkerson) -------------------------------------- 18
12. Maximum Flow (Dinic) ----------------------------------------------- 18
14. Min Cost Max Flow 2 ------------------------------------------------ 19
15. Stable Marriage ---------------------------------------------------- 21

16. Geometry Routines 1 ------------------------------------------------ 22
17. angle -------------------------------------------------------------- 22
18. squaredDistance ---------------------------------------------------- 23
19. distance ----------------------------------------------------------- 23
20. segmentToLine ------------------------------------------------------ 23
21. lineThroughPoint --------------------------------------------------- 23
22. segmentsIntersect -------------------------------------------------- 23
23. lineIntersectionPoint ---------------------------------------------- 24
24. segmentsIntersectionPoint ------------------------------------------ 24
25. segmentsIntersectionPoint2 ----------------------------------------- 25
26. pointOnLine -------------------------------------------------------- 26
27. multiply ----------------------------------------------------------- 26
28. pointInSegment ----------------------------------------------------- 26
29. rotate ------------------------------------------------------------- 26
30. circlesIntersect --------------------------------------------------- 27
31. pointToLineDistance ------------------------------------------------ 27
32. circleLineIntersectionPoints --------------------------------------- 27
33. circlesIntersectionPoints ------------------------------------------ 28
34. polygonArea -------------------------------------------------------- 28
35. convexHullGW ------------------------------------------------------- 29
36. convexHullGS ------------------------------------------------------- 30
37. polygonOriention --------------------------------------------------- 31
38. generalPolygonInclusion -------------------------------------------- 31
39. angleInclusion ----------------------------------------------------- 32
40. convexPolygonInclusion --------------------------------------------- 32
41. perpendicularProjection -------------------------------------------- 33
42. circleThroughPoints ------------------------------------------------ 33
43. cross -------------------------------------------------------------- 33
44. dot ---------------------------------------------------------------- 33
45. ang ---------------------------------------------------------------- 34
46. rotate ------------------------------------------------------------- 34
47. tangentToCircle ---------------------------------------------------- 34
48. circle2ptsRad ------------------------------------------------------ 35
49. triAreaFromMedians ------------------------------------------------- 35
50. segmentToPointDistance --------------------------------------------- 35
51. segmentsDistance --------------------------------------------------- 35
52. segmentToLineDistance ---------------------------------------------- 36

53. Geometry Routines 2 ------------------------------------------------ 36
54. leftTurn ----------------------------------------------------------- 36
55. distToLine --------------------------------------------------------- 36
56. distToLineSegment -------------------------------------------------- 36
57. lineIntersect ------------------------------------------------------ 36
58. greateCircle ------------------------------------------------------- 37

59. Aho-Corasick ------------------------------------------------------- 37
60. Suffix Tree -------------------------------------------------------- 40
61. Range Intersect + Difference --------------------------------------- 44
62. Polygon Halfplane Intersection ------------------------------------- 44
63. Knuth-Morris-Pratt ------------------------------------------------- 45
64. 3D Rotation Matrix ------------------------------------------------- 46
65. Ellipse Properties ------------------------------------------------- 46
66. Hyperbola Properties ----------------------------------------------- 47
67. Area Equation of Lattice Polygon ----------------------------------- 47

69. Number Theory ------------------------------------------------------ 47
70. Extended GCD ------------------------------------------------------- 47
71. Modular Linear Equation Solver ------------------------------------- 47
72. Linear Diophantine Equation Solver --------------------------------- 47
73. Modular Inverse ---------------------------------------------------- 48
74. Euler Totient Function --------------------------------------------- 48

75. Pair Sums ---------------------------------------------------------- 48
76. Binary Equation System --------------------------------------------- 49







































============================================================================
============================= CUT EGE ======================================
============================================================================
#define NODES 100
int n, graph[NODES][NODES], dfi[NODES], t, low[NODES];
bool mark[NODES];
vector<pair<int, int> > cut;
void dfsMatrix(int v, int p)
{
	mark[v] = true;
	dfi[v] = t++;
	low[v] = dfi[v];
	for (int i = 0; i < n; i++)
		if (i != p && graph[v][i] && mark[i] && dfi[i] < low[v])
			low[v] = dfi[i];
		else if (graph[v][i] && !mark[i])
		{
			dfsMatrix(i, v);
			if (low[i] < low[v])
				low[v] = low[i];
			if (low[i] == dfi[i])
				cut.push_back(make_pair(v, i));
		}
}
void cutEdgeMatrix()
{
	t = 0;
	memset(mark, false, n * sizeof(bool));
	cut = vector<pair<int, int> >();
	for (int i = 0; i < n; i++)
		if (!mark[i])
			dfsMatrix(i, -1);
}

============================================================================
============================= CUT VERTEX ===================================
============================================================================
#define NODES 100
vector<int> st;
vector<vector<int> > components;
void componentFound(int v)
{
	components.push_back(vector<int>());
	while (st.back() != v)
	{
		components.back().push_back(st.back());
		st.pop_back();
	}
	components.back().push_back(v);
}
int n, graph[NODES][NODES], dfi[NODES], t, low[NODES], f;
bool mark[NODES];
set<int> cut;
void dfsMatrix(int v)
{
	st.push_back(v);
	int branches = 0;
	mark[v] = true;
	dfi[v] = t++;
	low[v] = dfi[v] - 1;
	for (int i = 0; i < n; i++)
		if (graph[v][i] && mark[i] && dfi[i] < low[v])
			low[v] = dfi[i];
		else if (graph[v][i] && !mark[i])
		{
			branches++;
			dfsMatrix(i);
			if (low[i] < low[v])
				low[v] = low[i];
			if (low[i] == dfi[v])
			{
				if (v != f)
					cut.insert(v);
				componentFound(v);
			}
		}
		if (v == f && branches > 1)
			cut.insert(f);
}
void cutVertexMatrix()
{
	t = 0;
	memset(mark, false, n * sizeof(bool));
	cut = set<int>();
	st = vector<int>();
	components = vector<vector<int> >();
	for (int i = 0; i < n; i++)
		if (!mark[i])
		{
			dfsMatrix(f = i);
			st.pop_back();
		}
}

============================================================================
============================ EULERIAN TOUR =================================
============================================================================
typedef pair<int,int> _p;
int mark[50];
int graph[50][50];
int n;
void dfs(int v)
{
	mark[v]=1;
	for(int i=0;i<n;i++)
		if(!mark[i]&&graph[v][i])dfs(i);
}
list<_p> euler(int v)
{
	list<_p> local;
	while(graph[v][v])
		local.push_back(_p(v,v)),graph[v][v]-=2;
	int flag=0,ret=v;
	for(int i=0;i<n;i++)
		if(graph[v][i])
		{
			graph[v][i]--;
			graph[i][v]--;
			local.push_back(_p(v,i));
			v=i;
			while(v!=ret)
			{
				for(int j=0;j<n;j++)
					if(graph[v][j])
					{
						graph[v][j]--;
						graph[j][v]--;
						local.push_back(_p(v,j));
						v=j;
						break;
					}
			}
		}
		for(list<_p>::iterator i=local.begin();i!=local.end();i++)
		{
			list<_p> temp=euler(i->first);
			local.insert(i,temp.begin(),temp.end());
		}
		return local;
}
main()
{
	int N,m,a,b,flag;
	cin>>N;
	for(int z=1;z<=N;z++)
	{
		if(z>1)cout<<endl;
		cout<<"Case #"<<z<<endl;
		cin>>m;
		flag=n=0;
		memset(graph,0,sizeof graph);
		for(int i=0;i<m;i++)
		{
			cin>>a>>b;
			graph[a-1][b-1]++;
			graph[b-1][a-1]++;
			n=max(n,max(a,b));
		}
		dfs(n-1);
		for(int i=0;i<n;i++)
		{
			int d=0;
			for(int j=0;j<n;j++)
				d+=graph[i][j];
			if(d&1||!mark[i]&&d)
			{
				cout<<"some beads may be lost"<<endl;
				flag=1;break;
			}
		}
		if(!flag)
		{
			list<_p> l=euler(n-1);
			for(list<_p>::iterator i=l.begin();i!=l.end();i++)
				cout<<i->first+1<<' '<<i->second+1<<endl;
		}
	}
	return 0;
}

============================================================================
============================= BIG NUM ======================================
============================================================================

#define MAXLEN 10000
struct BigNum{
	short n[MAXLEN];
	int len;
} temp,one,zero,ans,res,up,xx;
void print(BigNum &a)
{
	for(int i=a.len-1;i+1;i--)cout<<a.n[i];
	cout<<endl;
}
void assignInt(BigNum &a,int n)
{
	int i=0;
	do {a.n[i++]=n%10;n/=10;}while(n);
	a.n[i]=-1;
	a.len=i;
}
void assignStr(BigNum &a,string n)
{
	int i=0,len=n.length();
	for(i=len-1;i+1;i--)
		a.n[len-1-i]=n[i]-'0';
	a.n[len]=-1;
	a.len=len;
}
void copyNum(BigNum &des,BigNum &src)
{
	int i;
	for(i=0;src.n[i]+1;i++)des.n[i]=src.n[i];
	des.n[i]=-1;
	des.len=i;
}
int numcmp(BigNum &a,BigNum &b)
{
	int l1=a.len,l2=b.len;
	if(l1!=l2)return l1>l2?1:-1;
	for(int i=l1-1;i+1;i--)
		if(a.n[i]!=b.n[i])return a.n[i]<b.n[i]?-1:1;
	return 0;
}
void add(BigNum &a,BigNum &b,BigNum &c)//c=a+b
{
	int i,t=0;
	for(i=0;a.n[i]>=0&&b.n[i]>=0;i++)
		c.n[i]=(t=(a.n[i]+b.n[i]+t))%10,t/=10;
	for(short *p=(a.n[i]==-1?&b.n[i]:&a.n[i]);*p!=-1;p++,i++)
		c.n[i]=(t=(*p+t))%10,t/=10;
	if(t)c.n[i++]=t;
	c.n[i]=-1;
	c.len=i;
}
void mul(BigNum &a,BigNum &b,BigNum &c)//c=a*b
{
	int t=0,tt,i,j;
	memset(c.n,0,sizeof(short)*MAXLEN);
	for(i=0;a.n[i]+1;i++)
	{
		for(j=0;b.n[j]+1;j++)
			tt=c.n[i+j]+a.n[i]*b.n[j]+t,c.n[i+j]=tt%10,t=tt/10;
		for(;t;j++)
			tt=c.n[i+j]+t,c.n[i+j]=tt%10,t=tt/10;
	}
	for(i+=j;!c.n[i]&&i;i--);
	c.n[i+1]=-1;
	c.len=i+1;
}
void div2(BigNum &a,BigNum &b)
{
	int i=a.len,t,j;
	b.n[t=i]=-1;
	b.len=i;
	for(i--,j=i;i+1;i--,j--)
		if((a.n[i]&1)&&i)
		{
			b.n[j]=a.n[i]/2;
			a.n[i-1]+=10;
		}else
			b.n[j]=a.n[i]/2;
		for(i=t-1;!b.n[i]&&i;b.len=i,b.n[i--]=-1);
}
void sub(BigNum &a,BigNum &b,BigNum &c)//c=a-b && should a>=b,a maybe
changed
{
	int i,j;
	for(i=0;a.n[i]+1&&b.n[i]+1;i++)
		if(a.n[i]-b.n[i]>=0)c.n[i]=a.n[i]-b.n[i];
		else
		{
			c.n[i]=10-b.n[i]+a.n[i];
			for(j=i+1;!a.n[j];j++)a.n[j]=9;
			a.n[j]--;
		}
		for(;a.n[i]+1;i++)c.n[i]=a.n[i];
		c.len=i;
		c.n[i--]=-1;
		while(i+1&&!c.n[i])c.n[i--]=-1,c.len--;
		if(i==-1)c.n[0]=0,c.len=1;
}
void removeZero(BigNum &n)//for use in div
{
	int i=n.len-1;
	while(!n.n[i]&&i)n.len--,n.n[i--]=-1;
}
void div(BigNum &a,BigNum &b,BigNum &r,BigNum &q)// a=b*Q+R
{
	BigNum sum[11],temp,temp1;
	int cmp=numcmp(a,b);
	if(!cmp)
	{
		assignInt(r,0);
		assignInt(q,1);
		return;
	}else if(cmp==-1)
	{
		copyNum(r,a);
		assignInt(q,0);
		return;
	}
	copyNum(sum[0],b);
	for(int i=1;i<11;i++)
		add(sum[i-1],b,sum[i]);
	int index=0,k;
	int first=b.len;
	copy(a.n+a.len-first,a.n+a.len,temp.n);
	temp.n[temp.len=first]=-1;
	if(numcmp(temp,b)<0)
		first++;
	copy(a.n+a.len-first,a.n+a.len,temp.n);
	temp.n[temp.len=first]=-1;
	int firstLen=a.len-first;
	while(1)
	{
		for(k=0;k<11;k++)
			if(numcmp(temp,sum[k])<0)
				break;
		q.n[index++]=k;
		sub(temp,sum[k-1],temp1);
		if(firstLen<1)break;
		for(int i=temp1.len+1;i;i--)
			temp1.n[i]=temp1.n[i-1];
		temp1.n[0]=a.n[--firstLen];
		temp1.len++;
		removeZero(temp1);
		while(numcmp(temp1,b)<0)
		{
			q.n[index++]=0;
			if(firstLen<1)break;
			for(int i=temp1.len+1;i;i--)
				temp1.n[i]=temp1.n[i-1];
			temp1.n[0]=a.n[--firstLen];
			temp1.len++;
			removeZero(temp1);
		}
		if(numcmp(temp1,b)<0)break;
		copyNum(temp,temp1);
	}
	copyNum(r,temp1);
	q.n[q.len=index]=-1;
	reverse(q.n,q.n+index);
}

============================================================================
======================= LINERA EQUATION SOLVER==============================
============================================================================
/*------------------------------------------------------------------*
* Linear Equation Solver
* * Solves a system of linear equations using Gauss Method.
* * You should :
* a) put equation matrix in mat[0..n - 1][0..n - 1]
* b) put array of answers in mat[n][0..n - 1]
* c) call solve(n)
*
* * Solve(n) returns :
* a) 0 : if system has a unique answer
* b) 1 : if system has infinite answers
* c) 2 : if system has no answers
*
* * It also fills mark[0..n - 1] with above flags (0, 1, 2) to
* indicate that the system had unique/infinite/no answer(s)
* for parameter[0..n - 1]
*
* * If the system has a unique answer for parameter[i] then after
* calling solve(n) the answer for parameter[i] equals:
* (mat[i][i] / mat[i][n])
*
*-----------------------------------------------------------------*/
#include <fstream>
#include <cmath>
#include <cstring>
using namespace std;
const double epsillon = 1e-6
;
double mat[100][101];
int mark[100];
int ZeroRow(int r, int n)
{
	for (int i = 0; i < n; i++)
		if (fabs(mat[r][i]) >= epsillon)
			return 0;
	return 1;
}
void AddRow(double a, int source, int target, int n)
{
	for (int i = 0; i < n + 1; i++)
		mat[target][i] += a * mat[source][i];
}
void ChangeRow(int source, int target, int n)
{
	double temp;
	for (int i = 0; i < n + 1; i++)
	{
		temp = mat[target][i];
		mat[target][i] = mat[source][i];
		mat[source][i] = temp;
	}
}
int Solve(int n)
{
	int i, j;
	int flag = 0;
	memset(mark, 0, sizeof(mark));
	for (i = 0; i < n; i++)
	{
		j = i;
		for (j = i; (fabs(mat[j][i]) < epsillon) && (j < n); j++);
		if ((j == n) && mark[i-1])
			j = i - 1;
		if (j == n)
		{
			flag = 1;
			mark[i] = 1;
		}
		if ((j != i) && (j != n))
			ChangeRow(j, i, n);
		if (j != n)
			for (j = 0; j < n; j++)
				if (j != i)
					AddRow((-mat[j][i] / mat[i][i]), i, j, n);
		for (j = 0; j < n; j++)
			if (fabs(mat[j][i]) < epsillon)
				mat[j][i] = 0;
	}
	if (flag == 1)
	{
		for (i = 0; i < n; i++)
			if (ZeroRow(i, n))
			{
				if ((fabs(mat[i][n]) >= epsillon))
				{
					mark[i]++;
					for(int m = 0; m < n; m++)
						if(!mark[m] && mat[m][i])
							mark[m] = 2;
					flag = 2;
				}
				else
				{
					for (int m = 0; m < n; m++)
						if (!mark[m] && mat[m][i])
							mark[m] = 1;
				}
			}
			return flag;
	}
	return 0;
}
int main()
{
	memset(mat, 0, sizeof(mat));
	mat[0][0] = 1; mat[0][1] = 1; mat[0][2] = 0; mat[0][3] = 1;mat[0][4] = 0;
	mat[1][0] = 1; mat[1][1] = 2; mat[1][2] = 0; mat[1][3] = 2;
	mat[1][4] = 0;
	mat[2][0] = 1; mat[2][1] = 3; mat[2][2] = 0; mat[2][3] = 3;
	mat[2][4] = 0;
	int n = 3;
	int res = Solve(n);
	int flag = 0;
	for(int i = 0; i < n; i++)
	{
		switch (mark[i])
		{
		case 0: cout << "X(" << i << ") = " << mat[i][n] / mat[i][i] << endl; break;
		case 1: cout << "X(" << i << ") has infinite Answers . . ." << endl;
			flag >?= 1; break;
		case 2: cout << "X(" << i << ") has no answers . . ." << endl; 
				flag >?= 2; break;
		}
	}
	cout << "So the equation has ";
	switch (flag)
	{ case 0: cout << "a Unique answer" << endl; break;
	  case 1: cout << "infinite answers" << endl; break;
	  case 3: cout << "no answers" << endl; break;
	}
	return 0;
}

============================================================================
========================== MATRIX INVERSION ================================
============================================================================
#define double int
typedef vector<double> Row;
typedef vector<Row> Matrix;
int p;
void swapRows(Matrix &matrix, int m, int n)
{
	Row tmp = matrix[m];
	matrix[m] = matrix[n];
	matrix[n] = tmp;
}
void addRow(Matrix &matrix, double coef, int m, int n)
{
	for (unsigned i = 0; i < matrix[m].size();i++)
	{
		matrix[n][i] += coef * matrix[m][i];
		matrix[n][i]%=p;
	}
}
void multiplyRow(Matrix &matrix, int n, double coef)
{
	for (unsigned i = 0; i < matrix[n].size();i++)
	{
		matrix[n][i] *= coef;
		matrix[n][i]%=p;
	}
}
int invt[30001];
int inv(int a)
{
	if(invt[a%p])return invt[a%p];
	for(int i=1;i<p;i++)
		if((a*i)%p==1)return invt[a%p]=i;
}
Matrix inverse(Matrix matrix)
{
	Matrix result(matrix.size(),Row(matrix.size()));
	unsigned i, j, k;
	for (i = 0; i < matrix.size(); i++)
		result[i][i] = 1;
	for (i = 0; i < matrix.size(); i++)
	{
		for (k = i; k < matrix.size() && !matrix[k][i]; k++);
		if (k == matrix.size())
			cout<<string("Given matrix is not invertible");
		swapRows(matrix, i, k);
		swapRows(result, i, k);
		for (j = 0; j < matrix.size(); j++)
		{
			if (j == i)
				continue;
			double coef = ((-matrix[j][i] *
				inv(matrix[i][i]))%p+p)%p;
			addRow(matrix, coef, i, j);
			addRow(result, coef, i, j);
		}
		double revCoef = inv(matrix[i][i]);
		multiplyRow(matrix, i, revCoef);
		multiplyRow(result, i, revCoef);
	}
	return result;
}
int pp(int a,int n)
{
	if(!n)return 1;
	int t=pp(a,n/2);
	t=(t*t)%p;
	if(n&1)
		t=(t*a)%p;
	return t;
}
int main()
{
	int N;
	char str[100];
	for(cin>>N;N--;)
	{
		cin>>p>>str;
		memset(invt,0,sizeof invt);
		int n=strlen(str);
		vector<Row>mat(n);
		for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				mat[i].push_back(pp(i+1,j));
		mat=inverse(mat);
		for(int i=0;i<n;i++)
		{
			int ans=0;
			for(int j=0;j<n;j++)
				ans+=(str[j]=='*'?0:str[j]-'a'+1)*mat[i][j];
			ans=((p+ans)%p+p)%p;
			cout<<ans<<' ';
		}
		cout<<endl;
	}
	return 0;
}


============================================================================
========================== POLYGON SIMILARITY ==============================
============================================================================

#define EPS 1e-10
#define N(i) ((i+1)%n)
#define P(i) ((i-1+n)%n)
#define p2(a) ((a)*(a))
using namespace std;
const double PI = 3.1415926535897932385;//2 * acos(0.)
inline bool dless(double x, double y)
{
	return x <= y - EPS;
}
inline double vectorAngle(double x, double y)
{
	double r = atan2(y, x);
	if (dless(r, 0))
		r += 2 * PI;
	return r;
}
inline double angle(double x1, double y1, double x2, double y2, double
					x3, double y3)
{
	double r=vectorAngle(x3-x2,y3-y2)-vectorAngle(x1-x2,y1-y2);
	if (dless(r, 0))
		r += 2 * PI;
	return r;
}
main()
{
	int n;
	double xf[10],xs[10],yf[10],ys[10];
	while(cin>>n,n)
	{
		for(int i=0;i<n;i++)
			cin>>xf[i]>>yf[i];
		for(int i=0;i<n;i++)
			cin>>xs[i]>>ys[i];
		double max1=0,max2=0;
		double len1[20],len2[10];
		double an1[20],an2[10];
		for(int i=0;i<n;i++)
		{
			double
				b1=sqrt(p2(xf[(i+1)%n]-xf[i])+p2(yf[(i+1)%n]-yf[i]));
			double
				b2=sqrt(p2(xs[(i+1)%n]-xs[i])+p2(ys[(i+1)%n]-ys[i]));
			len1[i]=b1;
			len2[i]=b2;
			max1=max(max1,b1);
			max2=max(max2,b2);
			an1[i]=angle(xf[P(i)],yf[P(i)],xf[i],yf[i],xf[N(i)],yf[N(i)
			]);
			an2[i]=angle(xs[P(i)],ys[P(i)],xs[i],ys[i],xs[N(i)],ys[N(i)
			]);
		}
		for(int i=0;i<n;i++)
		{
			len1[i]/=max1;
			len2[i]/=max2;
			len1[i+10]=len1[i];
			an1[i+10]=an1[i];
		}
		bool f=false;
		for(int i=0;i<n;i++)
		{
			bool f1=true;
			for(int j=0;j<n;j++)
				if(abs(len1[i+j]-len2[j])>=EPS
					||abs(an1[i+j]-an2[j])>=EPS)
				{
					f1=false;
					break;
				}
				if (f1)
				{
					f=true;
					break;
				}
		}
		if (f)
			cout<<"similar"<<endl;
		else
			cout<<"dissimilar"<<endl;
	}
	return 0;
}


============================================================================
========================== WEIGHTED MATCHING BABAK =========================
============================================================================
#include <cstring>
#include <iostream>
using namespace std;
#define MAXSIZE 100
#define INF 1000000000
int match[MAXSIZE];
bool dfs(int v, int n, int adj[MAXSIZE][MAXSIZE], int mark[], int s[], int t[])
{
	int i;
	s[v] = 1;
	mark[v] = 1;
	for (i = 0; i < n; i++)
		if (adj[v][i])
			if (t[i] = 1, match[i] == -1 || (!mark[match[i]] &&
				dfs(match[i], n, adj, mark, s, t)))
				return match[i] = v, true;
	return false;
}
bool matching(int n, int adj[MAXSIZE][MAXSIZE], int s[], int t[], int sa[])
{
	int i;
	int max = 0;
	int mark[MAXSIZE];
	memset(mark, 0, sizeof(mark));
	for (i = 0; i < n; i++)
		if (!sa[i] && !mark[i] && dfs(i, n, adj, mark, s, t))
		{
			memset(mark, 0, sizeof(mark));
			sa[i] = 1;
		}
		for (i = 0; i < n; i++)
			if (!sa[i])
				return false;
		return true;
}
void weighted(int n, int m, int weight[MAXSIZE][MAXSIZE])
{
	int i, j;
	int size = 0;
	int sa[MAXSIZE], s[MAXSIZE], t[MAXSIZE];
	int cover[2][MAXSIZE];
	int adj[MAXSIZE][MAXSIZE];
	memset(match, -1, sizeof(match));
	memset(sa, 0, sizeof(sa));
	memset(adj, 0, sizeof(adj));
	if (m > n)
		n = m;
	for (i = 0; i < n; i++)
	{
		int index = 0;
		for (j = 1; j < n; j++)
			if (weight[i][index] < weight[i][j])
				index = j;
		cover[1][i] = 0;
		cover[0][i] = weight[i][index];
		adj[i][index] = 1;
	}
	while (!matching(n, adj, s, t, sa))
	{
		memset(s, 0, sizeof(s));
		memset(t, 0, sizeof(t));
		matching(n, adj, s, t, sa);
		int min = INF;
		for (i = 0; i < n; i++)
			for (j = 0; j < n; j++)
				if (s[i] && !t[j] && !adj[i][j])
					if (cover[0][i] + cover[1][j] - weight[i][j] < min)
						min = cover[0][i] + cover[1][j] - weight[i][j];
		for (i = 0; i < n; i++)
			if (s[i])
				cover[0][i] -= min;
		for (i = 0; i < n; i++)
			if (t[i])
				cover[1][i] += min;
		for (i = 0; i < n; i++)
			for (j = 0; j < n; j++)
				if ((s[i] && !t[j]) || (!s[i] && t[j]))
					if ((cover[0][i] + cover[1][j]-weight[i][j])==0)
						adj[i][j] = 1;
					else
						adj[i][j] = 0;
	}
}
main()
{
	int i, j, tn;
	int n, m, sum;
	int weight[MAXSIZE][MAXSIZE];
	for (cin >> tn; tn--;)
	{
		memset(weight, 0, sizeof weight);
		cin >> n >> m;
		for (i = 0; i < n; i++)
			for (j = 0; j < m; j++)
				cin >> weight[i][j];
		weighted(n, m, weight);
		sum = 0;
		for (i = 0; i < max(n, m); i++)
		{
			if (i < m && match[i] < n)
			{
				cout << match[i] << ' ' << i << endl;
				sum += weight[match[i]][i];
			}
		}
		cout << sum << endl;
	}
	return 0;
}

============================================================================
=========================== STOER-WAGNER MINCUT ============================
============================================================================
#define NN 256
#define MAXW 1000
int g[NN][NN], v[NN], w[NN], na[NN];
bool a[NN];
int minCut( int n )
{
    for( int i = 0; i < n; i++ ) v[i] = i;
    int best = MAXW * n * n;
    while( n > 1 )
    {
        a[v[0]] = true;
        for( int i = 1; i < n; i++ )
        {
            a[v[i]] = false;
            na[i - 1] = i;
            w[i] = g[v[0]][v[i]];
        }
        int prev = v[0];
        for( int i = 1; i < n; i++ )
        {
            int zj = -1;
            for( int j = 1; j < n; j++ )
                if( !a[v[j]] && ( zj < 0 || w[j] > w[zj] ) )
                    zj = j;
            a[v[zj]] = true;
            if( i == n - 1 )
            {
                best <?= w[zj];
                for( int j = 0; j < n; j++ )
                    g[v[j]][prev] = g[prev][v[j]] += g[v[zj]][v[j]];
                v[zj] = v[--n];
                break;
            }
            prev = v[zj];
            for( int j = 1; j < n; j++ ) if( !a[v[j]] )
                w[j] += g[v[zj]][v[j]];
        }
    }
    return best;
}
int main()
{
    // read the graph's adjacency matrix into g[][]
    // and set n to equal the number of vertices
    int n, answer = minCut( n );
    return 0;
}

============================================================================
============================ BIPARTITE MATCHING ============================
============================================================================
#define M 128
#define N 128

bool graph[M][N];
bool seen[N];
int matchL[M], matchR[N];
int n, m;

bool bpm( int u )
{
    for( int v = 0; v < n; v++ ) if( graph[u][v] )
    {
        if( seen[v] ) continue;
        seen[v] = true;

        if( matchR[v] < 0 || bpm( matchR[v] ) )
        {
            matchL[u] = v;
            matchR[v] = u;
            return true;
        }
    }
    return false;
}

vector<int> vertex_cover()
{
	// Comment : Vertices on the left side (n side) are labeled like this : m+i where i is the index
	set<int> s, t, um; // um = UnMarked
	vector<int> vc;
	for(int i = 0; i < m; i++)
		if(matchL[i]==-1)
			s.insert(i), um.insert(i);
	while( um.size() )
	{
		int v = *(um.begin());
		for(int i = 0; i < n; i++)
			if( graph[v][i] && matchL[v]!=i)
			{
				t.insert(i);
				if( s.find(matchR[i]) == s.end())
					s.insert(matchR[i]), um.insert(matchR[i]);
			}
		um.erase(v);
	}
	for(int i = 0; i < m; i++)
		if( s.find(i) == s.end() )
			vc.push_back(i);
	for(set<int>::iterator i = t.begin(); i != t.end(); i++)
		vc.push_back((*i) + m);
	return vc;
}

int main()
{
    // Read input and populate graph[][]
    // Set m, n
    memset( matchL, -1, sizeof( matchL ) );
    memset( matchR, -1, sizeof( matchR ) );
    int cnt = 0;
    for( int i = 0; i < m; i++ )
    {
        memset( seen, 0, sizeof( seen ) );
        if( bpm( i ) ) cnt++;
    }
    vector<int> vc = vertex_cover();
    // cnt contains the number of happy pigeons
    // matchL[i] contains the hole of pigeon i or -1 if pigeon i is unhappy
    // matchR[j] contains the pigeon in hole j or -1 if hole j is empty
    // vc contains the Vertex Cover
    return 0;
}

============================================================================
======================== MAXIMUM FLOW (FORD FULKERSON) =====================
============================================================================
int cap[NN][NN];
int fnet[NN][NN];
int q[NN], qf, qb, prev[NN];

int fordFulkerson( int n, int s, int t )
{
    memset( fnet, 0, sizeof( fnet ) );
    int flow = 0;
    while( true )
    {
        memset( prev, -1, sizeof( prev ) );
        qf = qb = 0;
        prev[q[qb++] = s] = -2;
        while( qb > qf && prev[t] == -1 )
            for( int u = q[qf++], v = 0; v < n; v++ )
                if( prev[v] == -1 && fnet[u][v] - fnet[v][u] < cap[u][v] )
                    prev[q[qb++] = v] = u;
        if( prev[t] == -1 ) break;
        int bot = 0x7FFFFFFF;
        for( int v = t, u = prev[v]; u >= 0; v = u, u = prev[v] )
            bot <?= cap[u][v] - fnet[u][v] + fnet[v][u];
        for( int v = t, u = prev[v]; u >= 0; v = u, u = prev[v] )
            fnet[u][v] += bot;
        flow += bot;
    }
    return flow;
}

int main()
{
    memset( cap, 0, sizeof( cap ) );
    int numVertices = 100;
    // ... fill up cap with existing edges.
    // if the edge u->v has capacity 6, set cap[u][v] = 6.        
    cout << fordFulkerson( numVertices, s, t ) << endl;
    return 0;
}

============================================================================
=========================== MAXIMUM FLOW (DINIC) ===========================
============================================================================
/* prev contains the minimum cut. If prev[v] == -1, then v is not
 * reachable from s; otherwise, it is reachable.
 * RUNNING TIME: O(n^3)
*/
#define NN 1024
int cap[NN][NN], deg[NN], adj[NN][NN];
int q[NN], prev[NN];
int dinic( int n, int s, int t )
{
    int flow = 0;
    while( true )
    {
        memset( prev, -1, sizeof( prev ) );
        int qf = 0, qb = 0;
        prev[q[qb++] = s] = -2;
        while( qb > qf && prev[t] == -1 )
            for( int u = q[qf++], i = 0, v; i < deg[u]; i++ )
                if( prev[v = adj[u][i]] == -1 && cap[u][v] )
                    prev[q[qb++] = v] = u;
        if( prev[t] == -1 ) break;
        for( int z = 0; z < n; z++ ) if( cap[z][t] && prev[z] != -1 )
        {
            int bot = cap[z][t];
            for( int v = z, u = prev[v]; u >= 0; v = u, u = prev[v] )
                bot <?= cap[u][v];
            if( !bot ) continue;
            cap[z][t] -= bot;
            cap[t][z] += bot;
            for( int v = z, u = prev[v]; u >= 0; v = u, u = prev[v] )
            {
                cap[u][v] -= bot;
                cap[v][u] += bot;
            }
            flow += bot;
        }
    }
    return flow;
}
int main()
{
    memset( cap, 0, sizeof( cap ) );
    int n, s, t, m;
    scanf( " %d %d %d %d", &n, &s, &t, &m );
    while( m-- )
    {
        int u, v, c; scanf( " %d %d %d", &u, &v, &c );
        cap[u][v] = c;
    }
    memset( deg, 0, sizeof( deg ) );
    for( int u = 0; u < n; u++ )
        for( int v = 0; v < n; v++ ) if( cap[u][v] || cap[v][u] )
            adj[u][deg[u]++] = v;
    printf( "%d\n", dinic( n, s, t ) );
    return 0;
}

===========================================================================
============================== MINCOST MAXFLOW 2 ==========================
===========================================================================

/* fnet contains the flow network. Careful: both fnet[u][v] and
 * fnet[v][u] could be positive. Take the difference.
 * COMPLEXITY: O(m*log(m)*flow  <?  n*m*log(m)*fcost)
 **/
#include <iostream>
using namespace std;
#define NN 1024
int cap[NN][NN];
int cost[NN][NN];
int fnet[NN][NN], adj[NN][NN], deg[NN];
int par[NN], d[NN], q[NN], inq[NN], qs;
int pi[NN];
#define CLR(a, x) memset( a, x, sizeof( a ) )
#define Inf (INT_MAX/2)
#define BUBL { \
    t = q[i]; q[i] = q[j]; q[j] = t; \
    t = inq[q[i]]; inq[q[i]] = inq[q[j]]; inq[q[j]] = t; }
#define Pot(u,v) (d[u] + pi[u] - pi[v])
bool dijkstra( int n, int s, int t )
{
    CLR( d, 0x3F );
    CLR( par, -1 );
    CLR( inq, -1 );
    d[s] = qs = 0;
    inq[q[qs++] = s] = 0;
    par[s] = n;
    while( qs ) 
    {
        int u = q[0]; inq[u] = -1;
        q[0] = q[--qs];
        if( qs ) inq[q[0]] = 0;
        for( int i = 0, j = 2*i + 1, t; j < qs; i = j, j = 2*i + 1 )
        {
            if( j + 1 < qs && d[q[j + 1]] < d[q[j]] ) j++;
            if( d[q[j]] >= d[q[i]] ) break;
            BUBL;
        }
        for( int k = 0, v = adj[u][k]; k < deg[u]; v = adj[u][++k] )
        {
            if( fnet[v][u] && d[v] > Pot(u,v) - cost[v][u] ) 
                d[v] = Pot(u,v) - cost[v][par[v] = u];
            if( fnet[u][v] < cap[u][v] && d[v] > Pot(u,v) + cost[u][v] ) 
                d[v] = Pot(u,v) + cost[par[v] = u][v];
            if( par[v] == u )
            {
                if( inq[v] < 0 ) { inq[q[qs] = v] = qs; qs++; }
                for( int i = inq[v], j = ( i - 1 )/2, t;
                     d[q[i]] < d[q[j]]; i = j, j = ( i - 1 )/2 )
                     BUBL;
            }
        }
    }
    for( int i = 0; i < n; i++ ) if( pi[i] < Inf ) pi[i] += d[i];
    return par[t] >= 0;
}
#undef Pot

int mcmf4( int n, int s, int t, int &fcost )
{
    CLR( deg, 0 );
    for( int i = 0; i < n; i++ )
    for( int j = 0; j < n; j++ ) 
        if( cap[i][j] || cap[j][i] ) adj[i][deg[i]++] = j;
    CLR( fnet, 0 );
    CLR( pi, 0 );
    int flow = fcost = 0;
    while( dijkstra( n, s, t ) ) 
    {
        int bot = INT_MAX;
        for( int v = t, u = par[v]; v != s; u = par[v = u] )
            bot <?= fnet[v][u] ? fnet[v][u] : ( cap[u][v] - fnet[u][v] );
        for( int v = t, u = par[v]; v != s; u = par[v = u] )
            if( fnet[v][u] ) { fnet[v][u] -= bot; fcost -= bot * cost[v][u]; }
            else { fnet[u][v] += bot; fcost += bot * cost[u][v]; }
        flow += bot;
    }
    return flow;
}
int main()
{
  int numV;
  cin >> numV;
    memset( cap, 0, sizeof( cap ) );
    int m, a, b, c, cp;
    int s, t;
    cin >> m;
    cin >> s >> t;
    // fill up cap with existing capacities.
    // if the edge u->v has capacity 6, set cap[u][v] = 6.
    // for each cap[u][v] > 0, set cost[u][v] to  the
    // cost per unit of flow along the edge i->v
    for (int i=0; i<m; i++) {
      cin >> a >> b >> cp >> c;
      cost[a][b] = c; // cost[b][a] = c;
      cap[a][b] = cp; // cap[b][a] = cp;
    }
    int fcost;
    int flow = mcmf3( numV, s, t, fcost );
    cout << "flow: " << flow << endl;
    cout << "cost: " << fcost << endl;
    return 0;
}


===========================================================================
============================== STABLE MARRIAGE  ===========================
===========================================================================
/**
 * MAIN FUNCTION: stableMarriage()
 *      Takes a set of m men and n women, where each person has
 *      an integer preference for each of the persons of the opposite
 *      sex. Produces a matching of each man to some woman. The matching
 *      will have the following properties:
 *          - Each man is assigned a different woman (n must be at least m).
 *          - No two couples M1W1 and M2W2 will be unstable.
 *      Two couples are unstable if
 *          - M1 prefers W2 over W1 and
 *          - W1 prefers M2 over M1.
 * INPUTS:
 *      - m:        number of men.
 *      - n:        number of women (must be at least as large as m).
 *      - L[i][]:   the list of women in order of decreasing preference of man i.
 *      - R[j][i]:  the attractiveness of i to j.
 * OUTPUTS:
 *      - L2R[]:    the mate of man i (always between 0 and n-1)
 *      - R2L[]:    the mate of woman j (or -1 if single)
 * ALGORITHM:
 *      The algorithm is greedy and runs in time O(m^2).
 **/
#define MAXM 1024
#define MAXW 1024
int m, n;
int L[MAXM][MAXW], R[MAXW][MAXM];
int L2R[MAXM], R2L[MAXW];
int p[MAXM];
void stableMarriage()
{
    static int p[128];
    memset( R2L, -1, sizeof( R2L ) );
    memset( p, 0, sizeof( p ) );
    // Each man proposes...
    for( int i = 0; i < m; i++ )
    {
        int man = i;
        while( man >= 0 )
        {
            // to the next woman on his list in order of decreasing preference,
            // until one of them accepts;
            int wom;
            while( 1 )
            {
                wom = L[man][p[man]++];
                if( R2L[wom] < 0 || R[wom][man] > R[wom][R2L[wom]] ) break;
            }
            // Remember the old husband of wom.
            int hubby = R2L[wom];
            // Marry man and wom.
            R2L[L2R[man] = wom] = man;
            // If a guy was dumped in the process, remarry him now.
            man = hubby;
        }
    }
}

===========================================================================
============================== GEOMETRY ROUTINES 1 ========================
===========================================================================
inline double round(double x, int p)
{
	if (less(x, 0))
		return floor(x * pow(10., p) - .5) / pow(10., p);
	return floor(x * pow(10., p) + .5) / pow(10., p);
}

inline int sign(double x)
{
	return (less(x, 0) ? -1 : (greater(x, 0) ? 1 : 0));
}

inline double vectorAngle(double x, double y)
{
	double r = atan2(y, x);
/*
	(-Pi < r <= Pi): the following 'if' statement should be excluded
	(0 <= r < 2 * Pi): the following 'if' statement should be included
*/
	if (less(r, 0))
		r += 2 * PI;
	return r;
}

inline double angle(double x1, double y1, double x2, double y2, double x3, double y3)
/*
	angle (x1,y1)-(x2,y2)-(x3,y3)
*/
{
	double r = vectorAngle(x3 - x2, y3 - y2) - vectorAngle(x1 - x2, y1 - y2);
/*
	(-Pi < r <= Pi): the following 'if' statement should be excluded
	(0 <= r < 2 * Pi): the following 'if' statement should be included
*/
	if (less(r, 0))
		r += 2 * PI;
	return r;
}

inline double squaredDistance(double x1, double y1, double x2, double y2)
{
	return (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1);
}

inline double distance(double x1, double y1, double x2, double y2)
{
	return sqrt((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1));
}

inline void segmentToLine(double x1, double y1, double x2, double y2,
						  double &a, double &b, double &c)
{
	a = y2 - y1;
	b = x1 - x2;
	c = -y1 * b - x1 * a;
}

inline void lineThroughPoint(double x, double y, double m,
							 double &a, double &b, double &c)
{
	a = -m;
	b = 1;
	c = m * x - y;
}

bool segmentsIntersect(double x1, double y1, double x2, double y2,
					   double x3, double y3, double x4, double y4)
/*
	NOTE: when intersections at endpoints are valid, two intersecting
	          coincident segments are considered intersecting.
		  when intersections at endpoints are invalid, two intersecting
		      coincident segments are considered not intersecting.
		  it could be handled seperately!
*/
{
	if (greater(min(x1, x2), max(x3, x4)) || greater(min(x3, x4), max(x1, x2)) ||
		greater(min(y1, y2), max(y3, y4)) || greater(min(y3, y4), max(y1, y2)))
/*
	'greater'      : intersections at endpoints are valid
	'greaterEqual' :       //      //     //     // invalid
*/
		return false;
	return ((lessEqual(((x4 - x2) * (y1 - y2) - (y4 - y2) * (x1 - x2)) *
		               ((x3 - x2) * (y1 - y2) - (y3 - y2) * (x1 - x2)), 0)) &&
		    (lessEqual(((x1 - x4) * (y3 - y4) - (y1 - y4) * (x3 - x4)) *
			           ((x2 - x4) * (y3 - y4) - (y2 - y4) * (x3 - x4)), 0)));
/*
	'lessEqual' : intersections at endpoints are valid
	'less'      :       //      //     //     // invalid
*/
}

int linesIntersectionPoint(double a1, double b1, double c1,
						   double a2, double b2, double c2,
						   double &x, double &y)
/*
	return values:
		0: lines are parallel
		1: lines are intersecting at point (x, y)
		2: lines are the same
*/
{
	if (equal(a1 * b2, a2 * b1))
		if(equal(a1 , 0))
			return equal(b1 * c2, b2 * c1) * 2;
		else
			return equal(a1 * c2, a2 * c1) * 2;
	y = -(a1 * c2 - a2 * c1) / (a1 * b2 - a2 * b1);
	if (equal(a1, 0))
		x = -(b2 * y + c2) / a2;
	else
		x = -(b1 * y + c1) / a1;
	return 1;
}

int segmentsIntersectionPoint(double x1, double y1, double x2, double y2,
							  double x3, double y3, double x4, double y4,
							  double &x5, double &y5)
/*
	uses:
		segmentToLine(double, double, double, double, double, double, double)
		segmentsIntersect(double, double, double, double, double, double, double, double)
*/
/*
	return values:
		0: no intersection
		1: intersection at point (x5, y5)
		2: intersection is a line segment
*/
{

	if (!segmentsIntersect(x1, y1, x2, y2, x3, y3, x4, y4))
/*
	intersections at endpoints should be valid
*/
		return 0;
	double a1, b1, c1, a2, b2, c2;
	segmentToLine(x1, y1, x2, y2, a1, b1, c1);
	segmentToLine(x3, y3, x4, y4, a2, b2, c2);
	if (equal(a1 * b2, a2 * b1))
/*
	the segments are coincident and intersecting
*/
	{
		if (less(x1, x2))
		{
			if (equal(x2, x3) && equal(y2, y3) && greaterEqual(x4, x2) ||
				equal(x2, x4) && equal(y2, y4) && greaterEqual(x3, x2))
			{
				x5 = x2;
				y5 = y2;
				return 1;
			}
			if (equal(x1, x3) && equal(y1, y3) && lessEqual(x4, x1) ||
				equal(x1, x4) && equal(y1, y4) && lessEqual(x3, x1))
			{
				x5 = x1;
				y5 = y1;
				return 1;
			}
		} else
		{
			if (equal(x2, x3) && equal(y2, y3) && lessEqual(x4, x2) ||
			    equal(x2, x4) && equal(y2, y4) && lessEqual(x3, x2))
			{
				x5 = x2;
				y5 = y2;
				return 1;
			}
			if (equal(x1, x3) && equal(y1, y3) && greaterEqual(x4, x1) ||
				equal(x1, x4) && equal(y1, y4) && greaterEqual(x3, x1))
			{
				x5 = x1;
				y5 = y1;
				return 1;
			}
		}
/*
	one of the segments is lied on the other one
*/
		return 2;
	}
	y5 = -(a1 * c2 - a2 * c1) / (a1 * b2 - a2 * b1);
	if (equal(a1, 0))
		x5 = -(b2 * y5 + c2) / a2;
	else
		x5 = -(b1 * y5 + c1) / a1;
	return 1;
}

int segmentsIntersectionPoint2(double x1, double y1, double x2, double y2,
							   double x3, double y3, double x4, double y4,
							   double &x5, double &y5)
/*
	return values:
		7 important bits of the result value are:
			bit 0:	1 : segments are intersecting at (x5, y5)
					0 : segments are not intersecting
			bit 1:	1 : containing lines are parallel
					0 : containing lines are not parallel
			bit 2:	1 : containing lines are coincident
					0 : containing lines are not coincident
			bit 3:	1 : containing lines are intersecting on
						the extension of segment 1-2 at (x5, y5)
					0 : containing lines are not intersecting
						on the extension of segment 1-2
			bit 4:	1 : containing lines are intersecting on
						the extension of segment 2-1 at (x5, y5)
					0 : containing lines are not intersecting
						on the extension of segment 2-1
			bit 5:	1 : containing lines are intersecting on
						the extension of segment 3-4 at (x5, y5)
					0 : containing lines are not intersecting
						on the extension of segment 3-4
			bit 6:	1 : containing lines are intersecting on
						the extension of segment 4-3 at (x5, y5)
					0 : containing lines are not intersecting
						on the extension of segment 4-3
*/
{
	double rnum = (y1 - y3) * (x4 - x3) - (x1 - x3) * (y4 - y3);
	double den = (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3);
	double snum = (y1 - y3) * (x2 - x1) - (x1 - x3) * (y2 - y1);
	int res = 0;
	if (equal(den, 0))
	{
		res |= 2;
		if (equal(rnum, 0)) res |= 4;
		return res;
	}
	double r = rnum / den;
	double s = snum / den;
	x5 = x1 + r * (x2 - x1);
	y5 = y1 + r * (y2 - y1);
	if (greater(r, 1)) res |= 8;
	if (less(r, 0)) res |= 16;
	if (greater(s, 1)) res |= 32;
	if (less(s, 0)) res |= 64;
	return (res ? res : 1);
}

double multiply(double x1, double y1, double x2, double y2, double x3, double y3)
{
	return (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1);
}

int pointInSegment(double xp, double yp, double x1, double y1, double x2, double y2)
{
	return (equal(multiply(xp, yp, x1, y1, x2, y2), 0) &&
		greaterEqual(xp, min(x1, x2)) && lessEqual(xp, max(x1, x2)) &&
		greaterEqual(yp, min(y1, y2)) && lessEqual(yp, max(y1, y2)));
}

void rotate(double &x, double &y, double angle)
/*
	rotate (x, y) around (0, 0)
	angle should be in radians
*/
{
	double tx = x * cos(angle) - y * sin(angle);
	double ty = x * sin(angle) + y * cos(angle);
	x = tx;
	y = ty;
}

int circlesIntersect(double x1, double y1, double r1,
                     double x2, double y2, double r2)
/*
	return values:
		0: no intersection
		1: one intersection
		2: two intersections
		3: the circles are the same
*/
{
	if (equal(x1, x2) && equal(y1, y2) && equal(r1, r2))
		return 3;
	double d = distance(x1, y1, x2, y2);
	if (greater(d, r1 + r2) || less(d, fabs(r1 - r2)))
		return 0;
	if (equal(d, r1 + r2)||equal(d, abs(r1 - r2))
		return 1;
	return 2;
}

double pointToLineDistance(double x, double y,
						   double a, double b, double c)
{
	return fabs(a * x + b * y + c) / sqrt(a * a + b * b);
}

int circleLineIntersect(double x, double y, double r,
						double a, double b, double c)
/*
	return values:
		0: no intersection
		1: one intersection
		2: two intersections
*/
{
	double delta;
	if (equal(b, 0))
		delta = a * a * r * r - (a * x + c) * (a * x + c);
	else
		delta = b * b * ((a * a + b * b) * r * r - (a * x + b * y + c) * (a * x + b * y + c));
	return (less(delta, 0) ? 0 : (equal(delta, 0) ? 1 : 2));
}

int circleLineIntersectionPoints(double x, double y, double r,
								 double a, double b, double c,
								 double &x1, double &y1, double &x2, double &y2)
/*
	return values:
		0: no intersection
		1: one intersection at (x1, y1)
		2: two intersections at (x1, y1) and (x2, y2)
*/
{
	double delta;
	if (equal(b, 0))
		delta = a * a * r * r - (a * x + c) * (a * x + c);
	else
		delta = b * b * ((a * a + b * b) * r * r - (a * x + b * y + c) * (a * x + b * y + c));
	if (less(delta, 0))
		return 0;
	if (equal(delta, 0))
	{
		x1 = (-a * (a * x + b * y + c)) / (a * a + b * b);
		y1 = (-b * (a * x + b * y + c)) / (a * a + b * b);
		x1 += x;
		y1 += y;
		return 1;
	}
	if (equal(b, 0))
	{
		y1 = sqrt(delta) / a;
		y2 = -sqrt(delta) / a;
		x1 = x2 = -(a * x + c) / a;
	} else
	{
		x1 = (-a * (a * x + b * y + c) + sqrt(delta)) / (a * a + b * b);
		y1 = -(a * (x1 + x) + b * y + c) / b;
		x2 = (-a * (a * x + b * y + c) - sqrt(delta)) / (a * a + b * b);
		y2 = -(a * (x2 + x) + b * y + c) / b;
	}
	x1 += x; y1 += y;
	x2 += x; y2 += y;
	return 2;
}

int circlesIntersectionPoints(double x1,double y1,double r1,double x2,double y2,double r2,
		double &xp1,double &yp1,double &xp2,double &yp2)
{
	double a=atan2(y2 - y1, x2 - x1);
	double s=hypot(x1 - x2, y1 - y2);
	if(s > r1 + r2 + eps)return 0;
	double b=acos((r1 * r1 + s * s - r2 * r2) / (2 * r1 * s));
	if(abs((r1 * r1 + s * s - r2 * r2) / (2 * r1 * s))>1)//necessary for some situation due to precision
		b=(r1 * r1 + s * s - r2 * r2)>=0?0:PI;
	xp1=cos(a+b)*r1+x1;
	xp2=cos(a-b)*r1+x1;
	yp1=sin(a+b)*r1+y1;
	yp2=sin(a-b)*r1+y1;
	if(abs(s-r1-r2)<eps||abs(s-abs(r1-r2))<eps)
		return 1;
	if(s<abs(r1-r2)-eps)return 0;
	return 2;
}


double polygonArea(int n, double x[], double y[])
/*
	return value:
		positive: points are ordered counter-clockwise
		negative:   //    //    //   clockwise
*/
{
	double a = 0;
	for (int i = 1; i <= n; i++)
		a += (x[i - 1] * y[i % n] - x[i % n] * y[i - 1]);
	return a / 2;
}

void convexHullGW(int n, double x[], double y[], vector<int> &ch)
/*
	Convex Hull finding, Gift-Wrapping algorithm, O(n^2)
*/
{
/*
	note the array size
*/
	bool mark[1000];
	int i, p0, p1, p2;
/*
	find the first point, which is the lowest, leftmost point.
*/
	p0 = 0;
	for (i = 0; i < n; i++)
		if (less(y[i], y[p0]) || equal(y[i], y[p0]) && less(x[i], x[p0]))
			p0 = i;
	p1 = p0;
	fill(mark, mark + n, false);
	ch = vector<int>();
	while (true)
	{
		mark[p1] = true;
		ch.push_back(p1);
		p2 = -1;
		for (i = 0; i < n; i++)
			if (!mark[i] &&
				(p2 == -1 || less(multiply(x[p1], y[p1], x[p2], y[p2], x[i], y[i]), 0) ||
/*
	'less'    : counter-clockwise
	'greater' : clockwise
*/
				equal(multiply(x[p1], y[p1], x[p2], y[p2], x[i], y[i]), 0) &&
				greaterEqual(x[i], min(x[p1], x[p2])) && lessEqual(x[i], max(x[p1], x[p2])) &&
				greaterEqual(y[i], min(y[p1], y[p2])) && lessEqual(y[i], max(y[p1], y[p2]))))
/*
	maximum number of points : i, p1, p2, i, p1, p2
	minimum number of points : p2, p1, i, p2, p1, i
*/
				p2 = i;
		if (p2 == -1 || less(multiply(x[p0], y[p0], x[p1], y[p1], x[p2], y[p2]), 0)
/*
	'less'    : counter-clockwise
	'greater' : clockwise
*/
			/*|| (equal(multiply(x[p0], y[p0], x[p1], y[p1], x[p2], y[p2]), 0) &&
				greaterEqual(x[p2], min(x[p1], x[p0])) && lessEqual(x[p2], max(x[p1], x[p0])) &&
				greaterEqual(y[p2], min(y[p1], y[p0])) && lessEqual(y[p2], max(y[p1], y[p0])))*/)
/*
	maximum number of points : exclude the above 3 lines
	minimum number of points : include the above 3 lines
*/
			break;
		p1 = p2;
	}
}

struct CompCHGS
{
	int m;
	double *x, *y;
	CompCHGS(int m, double *x, double *y): m(m), x(x), y(y) {}
	bool operator()(const int i1, const int i2) const
	{
		return (greater((x[i1] - x[m]) * (y[i2] - y[m]), (x[i2] - x[m]) * (y[i1] - y[m])) ||
/*
	'greater' : counter-clockwise
	'less'    : clockwise
*/
			(equal((x[i1] - x[m]) * (y[i2] - y[m]), (x[i2] - x[m]) * (y[i1] - y[m])) &&
			greaterEqual(x[i1], min(x[i2], x[m])) && lessEqual(x[i1], max(x[i2], x[m])) &&
			greaterEqual(y[i1], min(y[i2], y[m])) && lessEqual(y[i1], max(y[i2], y[m]))));
	}
};

void convexHullGS(int n, double x[], double y[], vector<int> &ch)
/*
	Convex Hull finding, Graham Scan algorithm, O(n*log(n))
*/
{
/*
	note the array size
*/
	int sorted[1000], i, m = 0;
	for (i = 0; i < n; i++)
	{
		sorted[i] = i;
		if (less(y[i], y[m]) || (equal(y[i], y[m]) && less(x[i], x[m])))
			m = i;
	}
	sorted[0] = m;
	sorted[m] = 0;
/*
	the angles 1 to n - 1 should be sorted in ascending order. for each two equal angles,
	the angle with enpoint nearer to origin	should become first.
*/
	sort(sorted + 1, sorted + n, CompCHGS(m, x, y));
/*
	after the sort, order of the last equal angles should be reversed.
*/
	for (i = n - 1; i > 1 &&
		equal((x[sorted[i]] - x[m]) * (y[sorted[i - 1]] - y[m]),
		(x[sorted[i - 1]] - x[m]) * (y[sorted[i]] - y[m])); i--);
	if (i > 1) reverse(sorted + i, sorted + n);

	ch = vector<int>();
	ch.push_back(sorted[0]);
	if (n > 1)
	{
		ch.push_back(sorted[1]);
		for (i = 2; i < n; i++)
		{
			while (ch.size() > 1 &&
				greaterEqual(multiply(x[sorted[i]], y[sorted[i]], x[ch.back()], y[ch.back()],
				x[ch[ch.size() - 2]], y[ch[ch.size() - 2]]), 0))
/*
	'greater'      : counter-clockwise, maximum number of points
	'greaterEqual' : counter-clockwise, minimum number of points
	'less'         : clockwise, maximum number of points
	'lessEqual'    : clockwise, minimum number of points
*/
				ch.pop_back();
			ch.push_back(sorted[i]);
		}
/*
	maximum number of points : exclude the following 'if' statement
	minimum number of points : include the following 'if' statement
*/
		if (ch.size() > 2 && equal(multiply(x[ch.front()], y[ch.front()], x[ch.back()],
			y[ch.back()], x[ch[ch.size() - 2]], y[ch[ch.size() - 2]]), 0))
			ch.pop_back();
	}
}

int polygonOrientation(int n, double x[], double y[])
/*
	result values:
		 1 : counter-clockwise
		-1 : clockwise
*/
{
	int m = 0;
	for (int i = 1; i < n; i++)
		if (less(y[i], y[m]) || (equal(y[i], y[m]) && less(x[i], x[m])))
			m = i;
	return sign(multiply(x[m], y[m], x[(m + n - 1) % n], y[(m + n - 1) % n], x[(m + 1) % n], y[(m + 1) % n]));
}

int generalPolygonInclusion(int n, double x[], double y[], double xp, double yp)
/*
	return values:
		0: (xp, yp) is outside the polygon
		1: (xp, yp) is inside the polygon
		2: (xp, yp) is on the polygon side
*/
{
	int i;
	for (i = 1; i <= n; i++)
		if (pointInSegment(xp, yp, x[i - 1], y[i - 1], x[i % n], y[i % n]))
			return 2;
	int r = 0;
	for (i = 1; i <= n; i++)
		if ((lessEqual(y[i - 1], yp) && greater(y[i % n], yp)
			|| lessEqual(y[i % n], yp) && greater(y[i - 1], yp)) &&
			less(xp, ((x[i % n] - x[i - 1]) * (yp - y[i - 1]) /
			(y[i % n] - y[i - 1]) + x[i - 1])))
			r = !r;
	return r;
}

bool angleInclusion(double xo, double yo, double xa, double ya, double xb, double yb,
					double xp, double yp)
/*
	checks to see if we encounter point 'p' while sweeping angle 'a-o-b' from 'a' to 'b'
*/
{
	double ab = multiply(xo, yo, xa, ya, xb, yb);
	double ap = multiply(xo, yo, xa, ya, xp, yp);
	double bp = multiply(xo, yo, xb, yb, xp, yp);
	return (greaterEqual(ab, 0) && greaterEqual(ap, 0) && lessEqual(bp, 0)) ||
		(less(ab, 0) && (greaterEqual(ap, 0) || lessEqual(bp, 0)));
}


int convexPolygonInclusion(int n, double x[], double y[], double xp, double yp)
/*
	the polygon should have at least three points which are not on the same line.
*/
/*
	return values:
		0: (xp, yp) is outside the polygon
		1: (xp, yp) is inside the polygon
		2: (xp, yp) is on the polygon side
*/
{
	double xm, ym;
	int i;
/*
	the points are checked to be in counter-clockwise order
*/
	if (polygonOrientation(n, x, y) > 0)
	{
		reverse(x, x + n);
		reverse(y, y + n);
	}
/*
	find an internal point
*/
	for (i = 2; i < n; i++)
		if (!equal(multiply(x[0], y[0], x[1], y[1], x[i], y[i]), 0))
		{
			xm = (x[0] + x[1] + x[i]) / 3;
			ym = (y[0] + y[1] + y[i]) / 3;
			break;
		}
/*
	NOTE: as you see, this algorithm is of O(log(n)) if the above
	      O(n) computations are done before!
*/
	int f = 0, l = n;
	while (f < l - 1)
	{
		int m = (f + l) / 2;
		if (angleInclusion(xm, ym, x[f], y[f], x[m], y[m], xp, yp))
			l = m;
		else
			f = m;
	}
	double r = multiply(x[f], y[f], x[l % n], y[l % n], xp, yp);
	return (equal(r, 0) ? 2 : greater(r, 0));
}

int perpendicularProjection(double xp, double yp,
							double x1, double y1, double x2, double y2,
							double &x, double &y)
/*
	computes the point (x, y) of perpendicular projection of point (xp, yp)
	onto segment (x1, y1)-(x2, y2)
*/
/*
	results:
		-1 : the point is on backward extension of the line
		 0 : the point is in the line including endpoints
		 1 : the point is on ahead extension of the line
*/
{
	double l = squaredDistance(x1, y1, x2, y2);
	double r = ((y1 - yp) * (y1 - y2) - (x1 - xp) * (x2 - x1)) / l;
	x = x1 + r * (x2 - x1);
	y = y1 + r * (y2 - y1);
	return (less(r, 0) ? -1 : greater(r, 1));
}

bool circleThroughPoints(double x1, double y1, double x2, double y2, double x3, double y3,
						 double &x, double &y, double &r)
/*
	result values:
		false : the points are on a same extension
		true  : circle is (x, y, r)
*/
{
	double d = 2 * (y1 * x3 + y2 * x1 - y2 * x3 - y1 * x2 - y3 * x1 + y3 * x2);
	if (equal(d, 0))
		return false;
	x = (y2 * x1 * x1 - y3 * x1 * x1 - y2 * y2 * y1 + y3 * y3 * y1 +
	     x2 * x2 * y3 + y1 * y1 * y2 + x3 * x3 * y1 - y3 * y3 * y2 -
	     x3 * x3 * y2 - x2 * x2 * y1 + y2 * y2 * y3 - y1 * y1 * y3) / d;
	y = (x1 * x1 * x3 + y1 * y1 * x3 + x2 * x2 * x1 - x2 * x2 * x3 +
	     y2 * y2 * x1 - y2 * y2 * x3 - x1 * x1 * x2 - y1 * y1 * x2 -
	     x3 * x3 * x1 + x3 * x3 * x2 - y3 * y3 * x1 + y3 * y3 * x2) / d;
	r = sqrt((x1 - x) * (x1 - x) + (y1 - y) * (y1 - y));
	return true;
}
double cross(double ax,double ay,double bx,double by)
{
	   return ax*by-ay*bx;
}
double dot(double ax,double ay,double bx,double by)
{
	   return ax*bx+ay*by;
}
double ang(double ax,double ay,double bx,double by)
{
	   return atan2(cross(ax,ay,bx,by),dot(ax,ay,bx,by));
}
void rotate(double &px,double &py,double t)
{
	double x,y;
	x=px;
	y=py;
	px=x*cos(t)-y*sin(t);
	py=x*sin(t)+y*cos(t);
}
void rotate(double &px,double &py,double &pz,double vx,double vy,double vz,double t)
{
	double ty,tx;
	ty=ang(vz,vx,1,0);
	rotate(pz,px,ty);
	rotate(vz,vx,ty);
	tx=ang(vy,vz,0,1);
	rotate(py,pz,tx);
	rotate(px,py,t);
	rotate(py,pz,-tx);
	rotate(pz,px,-ty);
}

int tangantToCircle(double x,double y,double xc,double yc,double r,
			double &xp,double &yp,double &xp2,double &yp2)
{
	//return value: 0 point in on circle
	//				1 point is not on circle
	//				-1 point is inside circle
	double vx=x-xc;
	double vy=y-yc;
	double norm=sqrt(vx*vx+vy*vy);
	vx=r*vx/norm;
	vy=r*vy/norm;
	double d=hypot(x-xc,y-yc);
	if(less(d,r))
		return -1;
	double l=sqrt(d*d-r*r);
	if(equal(l,0))
	{
		xp2=xp=x,yp2=yp=y;
		return 0;
	}
	double teta=acos(l/d);
	teta=PI/2.-teta;
	rotate(vx,vy,teta);
	xp=vx+xc;
	yp=vy+yc;
	rotate(vx,vy,-2*teta);
	xp2=vx+xc;
	yp2=vy+yc;
	return 1;
}

/*********************************************
 * Circle of a given radius through 2 points *
 *********************************************
 * Computes the center of a circle containing the 2 given
 * points. The circle has the given radius. The returned
 * center is never to the right of the vector
 * (x1, y1)-->(x2, y2).
 * If this is possible, returns true and passes the center
 * through the ctr array. Otherwise, returns false.
 * #include <math.h>
 * FIELD TESTING:
 *      - Valladolid 10136: Chocolate Chip Cookies
 **/
bool circle2ptsRad( double x1, double y1, double x2, double y2, double r, double ctr[2] )
{
    double d2 = ( x1 - x2 ) * ( x1 - x2 ) + ( y1 - y2 ) * ( y1 - y2 );
    double det = r * r / d2 - 0.25;
    if( det < 0.0 ) return false;
    double h = sqrt( det );
    ctr[0] = ( x1 + x2 ) * 0.5 + ( y1 - y2 ) * h;
    ctr[1] = ( y1 + y2 ) * 0.5 + ( x2 - x1 ) * h;
    return true;
}

/******************************
 * Triangle Area from Medians *
 ******************************
 * Given the lengths of the 3 medians of a triangle,
 * returns the triangle's area, or -1 if it impossible.
 * WARNING: Deal with the case of zero area carefully.
 * #include <math.h>
 * FIELD TESTING:
 *      - Valladolid 10347: Medians
 **/
double triAreaFromMedians( double ma, double mb, double mc )
{
    double x = 0.5 * ( ma + mb + mc );
    double a = x * ( x - ma ) * ( x - mb ) * ( x - mc );
    if( a < 0.0 ) return -1.0;
    else return sqrt( a ) * 4.0 / 3.0;
}

double segmentToPointDistance(double x,double y,double x1,double y1,double x2,double y2)
{
	double X,Y;
	int ret=perpendicularProjection(x,y,x1,y1,x2,y2,X,Y);
	if(!ret)
		return sqrt(squaredDistance(X,Y,x,y));
	else return min(sqrt(squaredDistance(x,y,x1,y1)),
		sqrt(squaredDistance(x,y,x2,y2)));
}

double segmentsDistance(double x1,double y1,double x2,double y2,double x3,double y3,double x4,double y4)
{
	if(segmentsIntersect(x1,y1,x2,y2,x3,y3,x4,y4))
		return 0;
	double l1=min(segmentToPointDistance(x1,y1,x3,y3,x4,y4),segmentToPointDistance(x2,y2,x3,y3,x4,y4));
	double l2=min(segmentToPointDistance(x3,y3,x1,y1,x2,y2),segmentToPointDistance(x4,y4,x1,y1,x2,y2));
	return min(l1,l2);
}

double segmentToLineDistance(double a,double b,double c,double x1,double y1,double x2,double y2)
{
	double a1,b1,c1,X,Y;
	segmentToLine(x1,y1,x2,y2,a1,b1,c1);
	int ret=linesIntersectionPoint(a,b,c,a1,b1,c1,X,Y);
	double ans=pointToLineDistance(x1,y1,a,b,c);
	ans=min(ans,pointToLineDistance(x2,y2,a,b,c));
	if(ret==2)return 0;
	else if(ret==1)
		if(pointInSegment(X,Y,x1,y1,x2,y2))return 0;
	return ans;
}

===========================================================================
============================== GEOMETRY ROUTINES 2 ========================
===========================================================================
bool leftTurn( P a, P b, P c )
{
    return ( b.x - a.x ) * ( c.y - b.y ) - ( b.y - a.y ) * ( c.x - b.x ) > EPS;
}

double distToLine(double ax, double ay, double bx, double by, double px, double py, double *cpx, double *cpy )
{
    //Formula: cp = a + (p-a).(b-a) / |b-a|^2 * (b-a)
    double proj = ( ( px - ax ) * ( bx - ax ) + ( py - ay ) * ( by - ay ) ) /
                  ( ( bx - ax ) * ( bx - ax ) + ( by - ay ) * ( by - ay ) );
    *cpx = ax + proj * ( bx - ax );
    *cpy = ay + proj * ( by - ay );
    return dist( px, py, *cpx, *cpy );
}

double distToLineSegment(double ax, double ay, double bx, double by, double px, double py, double *cpx, double *cpy )
{
    if( ( bx - ax ) * ( px - ax ) + ( by - ay ) * ( py - ay ) < EPS )
    {
        *cpx = ax;
        *cpy = ay;
        return dist( ax, ay, px, py );
    }
    if( ( ax - bx ) * ( px - bx ) + ( ay - by ) * ( py - by ) < EPS )
    {
        *cpx = bx;
        *cpy = by;
        return dist( bx, by, px, py );
    }
    return distToLine( ax, ay, bx, by, px, py, cpx, cpy );
}

bool lineIntersect( P a, P b, P c, P d, P &r )
{
    P n; n.x = d.y - c.y; n.y = c.x - d.x;
    double denom = n.x * ( b.x - a.x ) + n.y * ( b.y - a.y );
    if( fabs( denom ) < EPS ) return false;
    double num = n.x * ( a.x - c.x ) + n.y * ( a.y - c.y );
    double t = -num / denom;
    r.x = a.x + t * ( b.x - a.x );
    r.y = a.y + t * ( b.y - a.y );
    return true;
}

/****************
 * Great Circle *
 ****************
 * Given two pairs of (latitude, longitude), returns the
 * great circle distance between them.
 * FIELD TESTING
 *      - Valladolid 535: Globetrotter
 **/
double greatCircle( double laa, double loa, double lab, double lob )
{
    double PI = acos( -1.0 ), R = 6378.0;
    double u[3] = { cos( laa ) * sin( loa ), cos( laa ) * cos( loa ), sin( laa ) };
    double v[3] = { cos( lab ) * sin( lob ), cos( lab ) * cos( lob ), sin( lab ) };
    double dot = u[0]*v[0] + u[1]*v[1] + u[2]*v[2];
    bool flip = false;
    if( dot < 0.0 )
    {
        flip = true;
        for( int i = 0; i < 3; i++ ) v[i] = -v[i];
    }
    double cr[3] = { u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0] };
    double theta = asin( sqrt( cr[0]*cr[0] + cr[1]*cr[1] + cr[2]*cr[2] ) );
    double len = theta * R;
    if( flip ) len = PI * R - len;
    return len;
}

===========================================================================
============================== AHO CORASICK ===============================
===========================================================================
void Union(set<int> &s1, set<int> &s2)
{
	for(set<int>::iterator i = s2.begin(); i != s2.end(); i++)
		s1.insert(*i);
}
void Print(set<int> &s1)
{
	for(set<int>::iterator i = s1.begin(); i != s1.end(); i++) cout << *i << " ";
	cout << endl;
}
int counter = 0;
int cnt = 0;
struct AhoFSM{
	struct AhoFSMNode{
		AhoFSMNode* next;
		char label;
		AhoFSM* link;
		AhoFSMNode(){next = 0;}
	}
	* go;
	~AhoFSM()
	{
		AhoFSMNode* p = go;
		while(p)
		{
			delete p->link;
			p = p->next;
		}
	}
	AhoFSM* fail;
	int label;
	set<int> out;
	AhoFSM(){go = 0; fail = 0; label = counter++;}
	void insert(char* s)
	{
		if(s[0] == 0)
		{
			out.insert(cnt);
			return;
		}
		AhoFSMNode* p = go, *q = 0;
		while(p)
		{
			if(p->label == s[0])
			{
				p->link->insert(s+1);
				return;
			}
			q = p;
			p = p->next;
		}
		p = new AhoFSMNode();
		p->label = s[0];
		p->link = new AhoFSM();
		p->link->insert(s+1);
		p->next = go;
		go = p;
	}
	AhoFSM* find(char ch)
	{
		AhoFSMNode* p = go;
		while(p)
		{
			if(p->label == ch)
				return p->link;
			p = p->next;
		}
		return 0;
	}
	void print(int level = 0)
	{
		AhoFSMNode* p = go;
		Print(out);
		while(p)
		{
			for(int i = 0; i < level; i++) cout << " ";
			cout << p->label << " " << endl;
			p->link->print(level+2);
			p = p->next;
		}
	}
	int getSize()
	{
		int result = sizeof(*this);
		AhoFSMNode* p = go;
		while(p)
		{
			result += p->link->getSize();
			p = p->next;
		}
		return result;
	}

	void Construct()
	{
		queue<AhoFSM*> q;
		AhoFSMNode* p = go;
		while(p)
		{
			p->link->fail = this;
			q.push(p->link);
			p = p->next;
		}
		while(!q.empty())
		{
			AhoFSM* r = q.front();
			q.pop();
			AhoFSMNode* u = r->go;
			while(u)
			{
				q.push(u->link);
				AhoFSM* v = r->fail;
				while(v!= this && v->find(u->label) == 0)
					v = v->fail;
				u->link->fail = v->find(u->label);
				if(u->link->fail == 0)
					u->link->fail = this;
				Union(u->link->out, u->link->fail->out);
				Print(u->link->out);
				u = u->next;
			}
		}
	}
};
bool found[1002];
void Search(AhoFSM *fsm, char* s)
{
	AhoFSM *root = fsm;
	int l = strlen(s);
	for(int i = 0; i < l; i++)
	{
		while(fsm && fsm->find(s[i]) == 0 && fsm != root)
			fsm = fsm->fail;
		if(!fsm) fsm = root;
		fsm = fsm->find(s[i]);
		if(fsm == 0)
			fsm = root;
		if(fsm->out.size())
		{
			for(set<int>::iterator it = fsm->out.begin(); it != fsm->out.end(); it++)
				found[*it] = true;
		}
	}
}
const int MAX_LENGTH = 100010;
char T[ MAX_LENGTH ];
int main()
{
	int t, q;cin >> t;
	cin.getline(T, MAX_LENGTH - 1);
	for(; t--;)
	{
		AhoFSM fsm;
		cin.getline(T, MAX_LENGTH - 2);
		int N = strlen(T) - 1;
		char ha[1002];
		cin >> q;
		cin.getline(ha, 1001);
		for(int i = 0; i < q; i++)
		{
			cnt = i;
			cin.getline(ha, 1001);
			fsm.insert(ha);
		}
		memset(found, 0, sizeof found);
		Search(&fsm, T);
		for(int i = 0; i < q; i++)
			if(found[i]) cout << "y" << endl;
			else cout << "n" << endl;
	}
    return 0;
};

===========================================================================
=============================== SUFFIX TREE  ==============================
===========================================================================
class Suffix {
    public :
        int origin_node;
        int first_char_index;
        int last_char_index;
        Suffix( int node, int start, int stop )
            : origin_node( node ),
              first_char_index( start ),
              last_char_index( stop ){};
        int Explicit(){ return first_char_index > last_char_index; }
        int Implicit(){ return last_char_index >= first_char_index; }
        void Canonize();
};
class Edge {
    public :
        int first_char_index;
        int last_char_index;
        int end_node;
        int start_node;
        void Insert();
        void Remove();
        Edge();
        Edge( int init_first_char_index,
              int init_last_char_index,
              int parent_node );
        int SplitEdge( Suffix &s );
        static Edge Find( int node, int c );
        static int Hash( int node, int c );
};
class Node {
    public :
        int suffix_node;
        Node() { suffix_node = -1; }
        static int Count;
};
const int MAX_LENGTH = 100010;
const int HASH_TABLE_SIZE = 100021;  //A prime roughly 10% larger
Edge Edges[ HASH_TABLE_SIZE ];
int Node::Count = 1;
Node Nodes[ MAX_LENGTH * 2 ];
char T[ MAX_LENGTH ];
int N;
Edge::Edge()
{
    start_node = -1;
}
Edge::Edge( int init_first, int init_last, int parent_node )
{
    first_char_index = init_first;
    last_char_index = init_last;
    start_node = parent_node;
    end_node = Node::Count++;
}
int Edge::Hash( int node, int c )
{
    return ( ( node << 8 ) + c ) % HASH_TABLE_SIZE;
}
void Edge::Insert()
{
    int i = Hash( start_node, T[ first_char_index ] );
    while ( Edges[ i ].start_node != -1 )
        i = ++i % HASH_TABLE_SIZE;
    Edges[ i ] = *this;
}
void Edge::Remove()
{
    int i = Hash( start_node, T[ first_char_index ] );
    while ( Edges[ i ].start_node != start_node ||
            Edges[ i ].first_char_index != first_char_index )
        i = ++i % HASH_TABLE_SIZE;
    for ( ; ; ) {
        Edges[ i ].start_node = -1;
        int j = i;
        for ( ; ; ) {
            i = ++i % HASH_TABLE_SIZE;
            if ( Edges[ i ].start_node == -1 )
                return;
            int r = Hash( Edges[ i ].start_node, T[ Edges[ i ].first_char_index ] );
            if ( i >= r && r > j )
                continue;
            if ( r > j && j > i )
                continue;
            if ( j > i && i >= r )
                continue;
            break;
        }
        Edges[ j ] = Edges[ i ];
    }
}
Edge Edge::Find( int node, int c )
{
    int i = Hash( node, c );
    for ( ; ; ) {
        if ( Edges[ i ].start_node == node )
            if ( c == T[ Edges[ i ].first_char_index ] )
                return Edges[ i ];
        if ( Edges[ i ].start_node == -1 )
            return Edges[ i ];
        i = ++i % HASH_TABLE_SIZE;
    }
}
int Edge::SplitEdge( Suffix &s )
{
    Remove();
    Edge *new_edge =
      new Edge( first_char_index,
                first_char_index + s.last_char_index - s.first_char_index,
                s.origin_node );
    new_edge->Insert();
    Nodes[ new_edge->end_node ].suffix_node = s.origin_node;
    first_char_index += s.last_char_index - s.first_char_index + 1;
    start_node = new_edge->end_node;
    Insert();
    return new_edge->end_node;
}
void Suffix::Canonize()
{
    if ( !Explicit() ) {
        Edge edge = Edge::Find( origin_node, T[ first_char_index ] );
        int edge_span = edge.last_char_index - edge.first_char_index;
        while ( edge_span <= ( last_char_index - first_char_index ) ) {
            first_char_index = first_char_index + edge_span + 1;
            origin_node = edge.end_node;
            if ( first_char_index <= last_char_index ) {
               edge = Edge::Find( edge.end_node, T[ first_char_index ] );
                edge_span = edge.last_char_index - edge.first_char_index;
            };
        }
    }
}
void AddPrefix( Suffix &active, int last_char_index )
{
    int parent_node;
    int last_parent_node = -1;

    for ( ; ; ) {
        Edge edge;
        parent_node = active.origin_node;
        if ( active.Explicit() ) {
            edge = Edge::Find( active.origin_node, T[ last_char_index ] );
            if ( edge.start_node != -1 )
                break;
        } else { //implicit node, a little more complicated
            edge = Edge::Find( active.origin_node, T[ active.first_char_index ] );
            int span = active.last_char_index - active.first_char_index;
            if ( T[ edge.first_char_index + span + 1 ] == T[ last_char_index ] )
                break;
            parent_node = edge.SplitEdge( active );
        }
        Edge *new_edge = new Edge( last_char_index, N, parent_node );
        new_edge->Insert();
        if ( last_parent_node > 0 )
            Nodes[ last_parent_node ].suffix_node = parent_node;
        last_parent_node = parent_node;
        if ( active.origin_node == 0 )
            active.first_char_index++;
        else
            active.origin_node = Nodes[ active.origin_node ].suffix_node;
        active.Canonize();
    }
    if ( last_parent_node > 0 )
        Nodes[ last_parent_node ].suffix_node = parent_node;
    active.last_char_index++;  //Now the endpoint is the next active point
    active.Canonize();
};
bool isPresent(char* s, int len)
{
	int start_node = 0;
	for(int i = 0; i < len; i++)
	{
		Edge edge = Edge::Find( start_node, s[i] );
		if(edge.start_node == -1)
			return 0;
		for(int j = edge.first_char_index; j != edge.last_char_index; j++)
			if(i >= len)
				return true;
			else if(s[i++] != T[j])
				return false;
		start_node = edge.end_node;
	}
	return true;
}

int main()
{
	int t, q;cin >> t;
	cin.getline(T, MAX_LENGTH - 1);
	for(; t--;)
	{
		cin.getline(T, MAX_LENGTH - 2);
		N = strlen(T) - 1;
		Suffix active(0, 0, -1);
		for(int i = 0; i <= N; i++ )
			AddPrefix(active, i);
		cin >> q;
		char ha[1002];
		cin.getline(ha, 1001);
		for(int i = 0; i < q; i++)
		{
			cin.getline(ha, 1001);
			if(isPresent(ha, strlen(ha)))
				cout << "y" << endl;
			else
				cout << "n" << endl;
		}
	}
    return 0;
};

===========================================================================
============================= RANGE INTERSECT  ============================
===========================================================================
list<PII> Intersect(list<PII> &a, list<PII> &b, list<PII> &diff)
{
	list<PII> result;
	diff.clear();
	list<PII>::iterator it1 = a.begin(), it2 = b.begin();
	while(it1 != a.end() && it2 != b.end())
	{
		if(it1->second < it2->first)
		{
			diff.push_back(*it1);
			it1++;
		}
		else if(it2->second < it1->first)
		{
			it2++;
		}
		else
		{
			int s = maxi(it1->first, it2->first);
			int e = mini(it1->second, it2->second);
			Add(result, s, e);
			Add(diff, it1->first, s-1);
			Add(diff, it1->second+1, e);
			if(e == it1->second && e == it2->second)
				it1++, it2++;
			else if(e == it1->second)
			{
				it2->first = e+1;
				it1++;
			}
			else
			{
				it1->first = e+1;
				it2++;
			}
		}
	}
	for(;it1 != a.end();it1++)
		diff.push_back(*it1);
	return result;
}

===========================================================================
=============================== HADI POLYCUT  =============================
===========================================================================
void cutPoly(list<Pt> &poly, Pt a, Pt b)
{
	list<Pt> result;
	if(poly.size() == 0)
		return;
	if(poly.size() == 1)
	{
		if(leftTurn(a, b, poly.back()))
			result.push_back(poly.back());
		poly = result;
		return;
	}
	#define LI list<Pt>::iterator 
	LI last = poly.end(); last--;
	bool lastin = leftTurn(a, b, *last);
	for(LI it = poly.begin(); it != poly.end(); it++)
	{
		bool thisin = leftTurn(a, b, *it);
		if(!thisin && lastin || thisin && !lastin)
		{
			Pt r;
			lineIntersect(a, b, *last, *it, r);
			result.push_back(r);
		}
		if(thisin)
			result.push_back(*it);
		last = it;
		lastin = leftTurn(a, b, *last);
	}
	poly.clear();
	Pt Last;
	for(LI it = result.begin(); it != result.end(); it++)
	{
		if(!(it != result.begin() && Equal(*it, Last)))
			poly.push_back(*it);
		Last = *it;
	}
	if(poly.size() > 1)
	{
		if(Equal(poly.front(), poly.back()))
			poly.pop_back();
	}
}


===========================================================================
========================= KNUTH-MORRIS-PRATT  =============================
===========================================================================

// KMP Overlap Computation
overlap[0] = -1;
for (int i = 0; pattern[i] != '\0'; i++) {
	overlap[i + 1] = overlap[i] + 1;
	while (overlap[i + 1] > 0 &&
		  pattern[i] != pattern[overlap[i + 1] - 1])
	  overlap[i + 1] = overlap[overlap[i + 1] - 1] + 1;
}

// KMP String Matching
j = 0;
for (i = 0; i < n; i++)
for (;;) {      // loop until break
  if (T[i] == P[j]) { // matches?
  j++;        // yes, move on to next state
  if (j == m) {   // maybe that was the last state
		found a match;
		j = overlap[j];
  }
  break;
  } else if (j == 0) break;   // no match in state j=0, give up
  else j = overlap[j];    // try shorter partial match
}



===========================================================================
========================= 3D ROTATION MATRIX ==============================
===========================================================================

Where c = cos (theta), s = sin (theta), t = 1-cos (theta), and <X,Y,Z> is the unit vector representing the arbitary axis

1. Left handed about arbitrary axis:
	
	tX^2+c		tXY-sZ		tXZ+sY	0
	tXY+sZ		tY^2+c		tYZ-sX	0
	tXZ-sY		tYZ+sX		tZ^2+c	0
		0				0				0		1
		
2. Right handed about arbitrary axis:
	
	tX^2+c		tXY+sZ		tXZ-sY	0
	tXY-sZ		tY^2+c		tYZ+sX	0
	tXZ+sY		tYZ-sX		tZ^2+c	0
		0				0				0		1
		
3. About X Axis
	1	0	0	0
	0	c	-s	0
	0	s	c	0
	0	0	0	1

4. About Y Axis
	c	0	s	0
	0	1	0	0
	-s	0	c	0
	0	0	0	1

5.	About Z Axis
	c	-s	0	0
	s	c	0	0
	0	0	1	0
	0	0	0	1
	
===========================================================================
========================= ELLIPSE PROPERTIES ==============================
===========================================================================

Equation = x^2 / a^2 + y^2 / b^2 = 1

Area = pi * a * b
Area of sector with angle theta = theta * a * b * 0.5

Perimeter = pi * a * b * (1 + h / 4 + h^2 / 64 + h^3 / 256 + ...)
where h = ((a-b) / (a+b))^2

Parametric Equation = (a * cos(theta), b * sin(theta))

Polar Equation: r = (a * b) / sqrt(a^2 * sin2(theta) + b^2 * cos2(theta))


===========================================================================
========================= HYPERBOLA PROPERTIES ============================
===========================================================================
Equation = x^2 / a^2 - y^2 / b^2 = 1
Paramteric Equation = (a * sec(theta), b * tan(theta))
Another Paramteric Equation = (a * cosh(theta), b * sinh(theta)) Which gives only one branch
Area of a sector = a * b * theta * 0.5
Polar Equation: r = (a * b) / sqrt(a^2 * sin2(theta) - b^2 * cos2(theta))

====================== AREA EQUATION OF LATICE POLYGON ====================
B / 2 + I - 1 = A

===========================================================================
============================== NUMBER THEORY ==============================
===========================================================================
template< class Int >
Triple< Int > egcd( Int a, Int b )
{
    if( !b ) return Triple< Int >( a, Int( 1 ), Int( 0 ) );
    Triple< Int > q = egcd( b, a % b );
    return Triple< Int >( q.d, q.y, q.x - a / b * q.y );
}

/**********************************
 * Modular Linear Equation Solver *
 **********************************
 * Given a, b and n, solves the equation ax = b (mod n)
 * for x. Returns the vector of solutions, all smaller
 * than n and sorted in increasing order. The vector is
 * empty if there are no solutions.
 * #include <vector>
 * REQUIRES: struct Triple, egcd
 **/
template< class Int >
vector< Int > msolve( Int a, Int b, Int n )
{
    if( n < 0 ) n = -n;
    Triple< Int > t = egcd( a, n );
    vector< Int > r;
    if( b % t.d ) return r;
    Int x = ( b / t.d * t.x ) % n;
    if( x < Int( 0 ) ) x += n;
    for( Int i = 0; i < t.d; i++ )
        r.push_back( ( x + i * n / t.d ) % n );
    return r;
}

/**************************************
 * Linear Diophantine Equation Solver *
 **************************************
 * Solves integer equations of the form ax + by = c
 * for integers x and y. Returns a triple containing
 * the answer (in .x and .y) and a flag (in .d).
 * If the returned flag is zero, then there are no
 * solutions. Otherwise, there is an infinite number
 * of solutions of the form
 *          x = t.x + k * b / t.d,
 *          y = t.y - k * a / t.d;
 * where t is the returned triple, and k is any
 * integer.
 * REQUIRES: struct Triple, egcd
 **/
template< class Int >
Triple< Int > ldioph( Int a, Int b, Int c )
{
    Triple< Int > t = egcd( a, b );
    if( c % t.d ) return Triple< Int >( 0, 0, 0 );
    t.x *= c / t.d; t.y *= c / t.d;
    return t;
}

/*******************
 * Modular Inverse *
 *******************
 * Given a and n, solves ax = 1 (mod n).
 * Returns 0 if there is no solution.
 * REQUIRES: struct Triple, egcd
 **/
template< class Int >
Int inverse( Int a, Int n )
{
    Triple< Int > t = egcd( a, n );
    if( t.d > Int( 1 ) ) return Int( 0 );
    Int r = t.x % n;
    return( r < Int( 0 ) ? r + n : r );
}

/**************************
 * Euler totient function *
 **************************
 * Returns the number of positive integers that are
 * relatively prime to n. As efficient as factor().
 * #include <vector>
 * REQUIRES: factor()
 * REQUIRES: sqrt() must work on Int.
 * REQUIRES: the constructor Int::Int( double ).
 **/
int phi( int n )
{
    vector< int > p;
    factor( n, p );
    for( int i = 0; i < ( int )p.size(); i++ )
    {
        if( i && p[i] == p[i - 1] ) continue;
        n /= p[i];
        n *= p[i] - 1;
    }
    return n;
}

===========================================================================
================================ PAIR SUMS ================================
===========================================================================

bool pairsums( int *ans, multiset< int > &seq )
{
    int N = seq.size();
    if( N < 3 ) return false;
    __typeof( seq.end() ) it = seq.begin();
    int a = *it++, b = *it++, i = 2;

    for( ; i * ( i - 1 ) < 2 * N && it != seq.end(); i++, ++it )
    {
        // assume seq[i] = ans[1] + ans[2]
        ans[0] = a + b - *it;
        if( ans[0] & 1 ) continue;
        ans[0] >>= 1;

        // try ans[0] as a possible least element
        multiset< int > seq2 = seq;
        int j = 1;
        while( seq2.size() )
        {
            ans[j] = *seq2.begin() - ans[0];
            for( int k = 0; k < j; k++ )
            {
                __typeof( seq2.end() ) jt = seq2.find( ans[k] + ans[j] );
                if( jt == seq2.end() ) goto hell;
                seq2.erase( jt );
            }
            j++;
        }
        hell:;
        if( j * ( j - 1 ) < 2 * N ) continue;

        // it worked! [modify this to deal with multiple answers]
        return true;
    }
    return false;
}


===========================================================================
=========================== BINARY EQUATION SYSTEM ========================
===========================================================================

The algorithm for this problem is analogous to row reducing a matrix. First, sort the rows in descending order by the first column. Break ties by
the second column, and so on. Now, find the leftmost 1 in the first row. For every other row that has a 1 in the same position, XOR that row with
the first row, in place. This will eliminate 1's from the leftmost column in every row but the first. Next, resort the rows, and find the leftmost
1 in the second row and repeat, removing all the 1's in that position except for one of them. Repeat this process until you get to the last row. Now,
if any of the rows have just a single 1 in the rightmost position (the answer column) then there are 0 valid functions, as you can't get a 1 by XORing
a bunch of 0's. Otherwise, we want to count the free variables. A variable is free if whenever there is 1 in the column that represents that variable,
there is another 1 in the same row that is further left (this is trivially true when there is no column containing a 1 for that variable). Finally, the
answer is simply 2number of free variables. This is because we can assign the free variables however we want, and once we've assigned them, each of the
bound (not free) variables must be assigned in a certain way to make the equations all true. For instance, lets say that you start out with the following
matrix:

010101
010010
001011
000111

Its already sorted properly, so first we remove the 1's from the second column by XORing the first row into the second:

010101        010101
000111  SORT  001011
001011  --->  000111
000111        000111

Now, we don't have to remove any 1's from the third column, as there is already only one row with a 1 there, so we move on to the third row. Now, we XOR
that row into the first and fourth rows and get:

010010
001011
000111
000000

Here, we are done. There are no rows that have just a 1 in the rightmost position, so there is at least one solution. The variables corresponding to the
first and fifth columns are free, so we can make both of them either 0 or 1, and thus there are 4 valid solutions. You can verify that for each of the 4
choices for the first and fifth variables, there is only one possibility for the bound variables.

An implementation detail is that if you use a 64 bit integer for each row, all of the coding becomes pretty simple.


#ifndef ALGORITHMEXECUTOR_HPP
#define ALGORITHMEXECUTOR_HPP
#include <iostream>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
using namespace std;
typedef unsigned int uint;
template <typename  T>
class AlgorithmExecutor    
{
private:
    
    uint m_dfsCnt;
    vector<uint> m_idomVector;
    vector<uint> m_sdomVector;
    vector<uint> m_index2dfs;
    vector<uint> m_index2ufs;
    vector<uint> m_index2val;
    vector<uint> m_index2rak;
    vector<uint> m_index2father;
    set<T> m_index2idSet;
    vector<T> m_index2id;
    map<T,uint>  m_id2index;
    vector<uint> m_startVectorCopy;
    vector<uint> m_endVectorCopy;
    uint m_edgeNum;
    uint m_nodeNum;
    uint* m_forwardGraphSize;
    uint* m_backwardGraphSize;
    uint** m_forwardGraph;
    uint** m_backwardGraph;

    vector<vector<uint>> m_mustPassNodeTree;
    vector<unordered_set<uint>> m_DF;
private:
    void dfsSearch(uint n);
    uint dfsFind(uint n);
    void buildforwardAndBackwardTree(void);
    void treeMapId2index(vector<T>& m_startVector,vector<T>& m_endVector);
    vector<T> privateGetDominantTreeIdom(vector<T>& m_startVector,vector<T>& m_endVector);
    vector<T> treeMapIndex2id(void);
    void initAllVar(void);
   
    void computeDF(uint node);
    
public:
    AlgorithmExecutor();
    ~AlgorithmExecutor(){};
    static AlgorithmExecutor<T>* createAlgorithmExecutor(void){return new AlgorithmExecutor<uint>();};
    vector<T> getDominantTreeIdom(vector<T>& m_startVector,vector<T>& m_endVector);
    vector<T> getUnreachableNodeList(vector<T>& m_startVector,vector<T>& m_endVector,T headNode);
    vector<vector<T>> getDominantFrontier(vector<T>& m_startVector,vector<T>& m_endVector);
    vector<vector<uint>> calculPhiNode(vector<vector<uint>>& Defs,vector<vector<uint>>& DF);
};

template <typename  T>
AlgorithmExecutor<T>::AlgorithmExecutor()
{
    m_dfsCnt = 0;
    m_idomVector.clear();
    m_sdomVector.clear();
    m_index2dfs.clear();
    m_index2ufs.clear();
    m_index2val.clear();
    m_index2rak.clear();
    m_index2father.clear();
    m_index2idSet.clear();
    m_index2id.clear();
    m_id2index.clear();
    m_startVectorCopy.clear();
    m_endVectorCopy.clear();
    m_edgeNum = 0;
    m_nodeNum = 0;
    m_forwardGraphSize = NULL;
    m_backwardGraphSize = NULL;
    m_forwardGraph = NULL;
    m_backwardGraph = NULL;

    vector<vector<uint>> m_mustPassNodeTree;
    vector<unordered_set<uint>> m_DF;    
}

template <typename  T>
void AlgorithmExecutor<T>::treeMapId2index(vector<T>& m_startVector,vector<T>& m_endVector)
{
    m_index2idSet.clear();
    m_id2index.clear();
    m_edgeNum = m_startVector.size();
    m_startVectorCopy.resize(m_edgeNum);
    m_endVectorCopy.resize(m_edgeNum);
    for(uint i = 0;i < m_edgeNum;i++)
    {
        m_index2idSet.insert(m_startVector[i]);
        m_index2idSet.insert(m_endVector[i]);
    }
    m_index2id.resize(m_index2idSet.size()+1);
    m_index2id[0] = 0;
    typename set<T>::iterator it = m_index2idSet.begin();
    for(uint i = 1;it!=m_index2idSet.end();it++,i++)
    {
        m_index2id[i] = *it;
        m_id2index[*it] = i;
    }
    for(uint i = 0;i < m_edgeNum;i++)
    {
        m_startVectorCopy[i] = m_id2index[m_startVector[i]];
        m_endVectorCopy[i] = m_id2index[m_endVector[i]];
    }
}
template <typename  T>
void AlgorithmExecutor<T>::buildforwardAndBackwardTree(void)
{
    m_nodeNum = m_index2idSet.size();
    m_edgeNum = m_startVectorCopy.size();
    m_forwardGraphSize = new uint[m_nodeNum + 2];
    m_backwardGraphSize = new uint[m_nodeNum + 2];
    for(uint i = 1;i <= m_nodeNum + 1;i++)
    {
        m_forwardGraphSize[i] = 0;
        m_backwardGraphSize[i] = 0;
    }
    for(uint i = 0;i < m_edgeNum;i++)
    {
        m_forwardGraphSize[m_startVectorCopy[i]]++;
        m_backwardGraphSize[m_endVectorCopy[i]]++;
    }
    uint *forwardInDegree = m_backwardGraphSize;
    
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        if(forwardInDegree[i] == 0)
        {
            m_forwardGraphSize[m_nodeNum+1]++;
            m_backwardGraphSize[i]++;
            m_edgeNum++;
        }
    }
    uint* forwardGraphSpace = new uint[m_edgeNum];
    uint* backwardGraphSpace = new uint[m_edgeNum];
    m_forwardGraph = new uint*[m_nodeNum + 2];
    m_backwardGraph = new uint*[m_nodeNum + 2];
    int needApplyforwardGraphSpaceLen = 0;
    int needApplybackwardGraphSpaceLen = 0;
    for(uint i = 1;i <= m_nodeNum+1;i++)
    {
        m_forwardGraph[i] = forwardGraphSpace + needApplyforwardGraphSpaceLen;
        m_backwardGraph[i] = backwardGraphSpace + needApplybackwardGraphSpaceLen;
        needApplyforwardGraphSpaceLen += m_forwardGraphSize[i];
        needApplybackwardGraphSpaceLen += m_backwardGraphSize[i];
        m_forwardGraphSize[i] = 0;
        m_backwardGraphSize[i] = 0;
    }
    for(uint i = 0;i < m_startVectorCopy.size();i++)
    {
        int startPoint = m_startVectorCopy[i];
        int endPoint = m_endVectorCopy[i];
        m_forwardGraph[startPoint][m_forwardGraphSize[startPoint]++] = endPoint;
        m_backwardGraph[endPoint][m_backwardGraphSize[endPoint]++] = startPoint;
    }
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        if(forwardInDegree[i] == 0)
        {
            m_forwardGraph[m_nodeNum+1][m_forwardGraphSize[m_nodeNum+1]++] = i;
            m_backwardGraph[i][m_backwardGraphSize[i]++] = m_nodeNum+1;
        }
    }    
}

template <typename  T>
vector<T> AlgorithmExecutor<T>::privateGetDominantTreeIdom(vector<T>& m_startVector,vector<T>& m_endVector)
{

    treeMapId2index(m_startVector,m_endVector);
    buildforwardAndBackwardTree();
    m_dfsCnt = 0;
    m_index2dfs.resize(m_nodeNum+2);
    m_index2val.resize(m_nodeNum+2);
    m_index2ufs.resize(m_nodeNum+2);
    m_index2rak.resize(m_nodeNum+2);
    m_index2father.resize(m_nodeNum+2);
    m_sdomVector.resize(m_nodeNum+2);
    m_idomVector.resize(m_nodeNum+2);
    for(uint i = 1;i <= m_nodeNum + 1;i++)
    {
        m_index2dfs[i] = 0;
        m_index2val[i] = i;
        m_index2ufs[i] = i;
    }
    dfsSearch(m_nodeNum+1);

    vector<vector<uint>> SpVector;
    SpVector.resize(m_nodeNum+2);
    for(uint i = m_nodeNum+1;i >= 2;i--)
    {
        uint node = m_index2rak[i];
        for(uint j = 0;j < m_backwardGraphSize[node];j++)
        {
            uint backNode = m_backwardGraph[node][j];
            dfsFind(backNode);
            m_sdomVector[node] = min(m_sdomVector[node],
                    m_sdomVector[m_index2val[backNode]]);
        }
        m_index2ufs[node] = m_index2father[node];
        SpVector[m_index2rak[m_sdomVector[node]]].push_back(node);
        for(uint j = 0;j < SpVector[m_index2father[node]].size();j++)
        {
            uint backNode = SpVector[m_index2father[node]][j];
            dfsFind(backNode);
            if(m_sdomVector[m_index2val[backNode]] == m_sdomVector[backNode])
                m_idomVector[backNode] = m_index2rak[m_sdomVector[backNode]];
            else m_idomVector[backNode] = m_index2val[backNode];
        }
        SpVector[m_index2father[node]].clear();
    }
    for(uint i = 1;i <= m_nodeNum+1;i++)
    {
        uint node = m_index2rak[i];
        if(m_idomVector[node] != m_index2rak[m_sdomVector[node]])
            m_idomVector[node] = m_idomVector[m_idomVector[node]];
    }
    vector<T> result = treeMapIndex2id();
    return result;
}

template <typename  T>
vector<T> AlgorithmExecutor<T>::getDominantTreeIdom(vector<T>& m_startVector,vector<T>& m_endVector)
{
    vector<T> result;
    result = privateGetDominantTreeIdom(m_startVector, m_endVector);
    initAllVar();
    return result;
}

template <typename  T>
void AlgorithmExecutor<T>::dfsSearch(uint n)
{
    m_sdomVector[n] = m_index2dfs[n] = ++m_dfsCnt;
    m_index2rak[m_dfsCnt] = n;
    for(uint i = 0;i<m_forwardGraphSize[n];i++)
    {
        uint node = m_forwardGraph[n][i];
        if(m_index2dfs[node] == 0)
        {
            dfsSearch(node);
            m_index2father[node] = n;
        }
    }
}

template <typename  T>
uint AlgorithmExecutor<T>::dfsFind(uint n)
{
    if(m_index2ufs[n] == n)return n;
    uint node = dfsFind(m_index2ufs[n]);
    if(m_sdomVector[m_index2val[m_index2ufs[n]]]
        < m_sdomVector[m_index2val[n]])
        m_index2val[n] = m_index2val[m_index2ufs[n]];
    m_index2ufs[n] = node;
    return node;
}

template <typename  T>
vector<T> AlgorithmExecutor<T>::treeMapIndex2id(void)
{
    vector<T> result;
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        int idomId = m_idomVector[i];
        result.push_back(m_index2id[i]);
        if(idomId == m_nodeNum+1)result.push_back(m_index2id[i]);
        else result.push_back(m_index2id[idomId]);
    }
    return result;
}

template <typename  T>
void AlgorithmExecutor<T>::initAllVar(void)
{
    m_dfsCnt = 0;
    m_idomVector.clear();
    m_sdomVector.clear();
    m_index2dfs.clear();
    m_index2ufs.clear();
    m_index2val.clear();
    m_index2rak.clear();
    m_index2father.clear();
    m_index2idSet.clear();
    m_index2id.clear();
    m_id2index.clear();
    m_startVectorCopy.clear();
    m_endVectorCopy.clear();
    m_edgeNum = 0;
    m_nodeNum = 0;

    for(uint i = 1;i <= m_nodeNum+1;i++)
    {
        if(m_forwardGraphSize[i] != 0)
            delete [] m_forwardGraph[i];
        if(m_backwardGraphSize[i] != 0)
            delete [] m_backwardGraph[i];        
    }
    delete [] m_forwardGraph;
    delete [] m_backwardGraph;  
    delete [] m_forwardGraphSize;
    delete [] m_backwardGraphSize;  
}

template <typename  T>
vector<T> AlgorithmExecutor<T>::getUnreachableNodeList(vector<T>& m_startVector,vector<T>& m_endVector,T headNode)
{
    treeMapId2index(m_startVector,m_endVector);
    headNode = m_id2index[headNode];
    m_nodeNum = m_index2idSet.size();
    m_edgeNum = m_startVectorCopy.size();
    m_forwardGraphSize = new uint[m_nodeNum + 2];
    m_backwardGraphSize = new uint[m_nodeNum + 2];
    for(uint i = 1;i <= m_nodeNum + 1;i++)
    {
        m_forwardGraphSize[i] = 0;
        m_backwardGraphSize[i] = 0;
    }
    for(uint i = 0;i < m_edgeNum;i++)
    {
        m_forwardGraphSize[m_startVectorCopy[i]]++;
        m_backwardGraphSize[m_endVectorCopy[i]]++;
    }

    uint* forwardGraphSpace = new uint[m_edgeNum];
    uint* backwardGraphSpace = new uint[m_edgeNum];
    m_forwardGraph = new uint*[m_nodeNum+2];
    m_backwardGraph = new uint*[m_nodeNum+2];
    int needApplyforwardGraphSpaceLen = 0;
    int needApplybackwardGraphSpaceLen = 0;
    for(int i = 1;i <= m_nodeNum;i++)
    {
        m_forwardGraph[i] = forwardGraphSpace + needApplyforwardGraphSpaceLen;
        m_backwardGraph[i] = backwardGraphSpace + needApplybackwardGraphSpaceLen;
        needApplyforwardGraphSpaceLen += m_forwardGraphSize[i];
        needApplybackwardGraphSpaceLen += m_backwardGraphSize[i];
        m_forwardGraphSize[i] = 0;
        m_backwardGraphSize[i] = 0;
    }
    for(uint i = 0;i < m_startVectorCopy.size();i++)
    {
        int startPoint = m_startVectorCopy[i];
        int endPoint = m_endVectorCopy[i];
        m_forwardGraph[startPoint][m_forwardGraphSize[startPoint]++] = endPoint;
        m_backwardGraph[endPoint][m_backwardGraphSize[endPoint]++] = startPoint;
    }
    m_dfsCnt = 0;
    m_index2dfs.resize(m_nodeNum+1);
    m_index2val.resize(m_nodeNum+1);
    m_index2ufs.resize(m_nodeNum+1);
    m_index2rak.resize(m_nodeNum+1);
    m_index2father.resize(m_nodeNum+1);
    m_sdomVector.resize(m_nodeNum+1);
    m_idomVector.resize(m_nodeNum+1);
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        m_index2dfs[i] = 0;
        m_index2val[i] = i;
        m_index2ufs[i] = i;
    }
    dfsSearch(headNode);
    vector<T> result;
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        if(m_index2dfs[i] == 0)result.push_back(m_index2id[i]);
    }
    initAllVar();
    return result;
}

template <typename  T>
vector<vector<T>> AlgorithmExecutor<T>::getDominantFrontier(vector<T>& m_startVector,vector<T>& m_endVector)
{
  
    vector<vector<T>> result;
    privateGetDominantTreeIdom(m_startVector, m_endVector);
    result.resize(m_nodeNum + 1);
    for(uint i = 0;i < m_nodeNum + 1;i++)result[i].clear();
    m_mustPassNodeTree.resize(m_nodeNum+1);
    m_DF.resize(m_nodeNum+1);
    for(uint i = 0;i<m_nodeNum+1;i++)m_mustPassNodeTree[i].clear();
    for(uint i = 0;i<m_nodeNum+1;i++)m_DF[i].clear();
    for(uint i = 1;i <= m_nodeNum;i++)
    {
        uint idomNode = m_idomVector[i];
        if(idomNode != m_nodeNum+1)
            m_mustPassNodeTree[idomNode].push_back(i);
    }
    uint headNode = 1;
    while(m_idomVector[headNode] != m_nodeNum+1)headNode = m_idomVector[headNode];
    computeDF(headNode);
    for(uint i = 1;i < m_nodeNum+1;i++)result[0].push_back(m_index2id[i]);
    for(uint i = 1;i < m_nodeNum+1;i++)
    {
        for(unordered_set<uint>::iterator it = m_DF[i].begin(); it != m_DF[i].end(); ++it)
        {
            result[i].push_back(m_index2id[*it]);
        }
    }
    initAllVar();
    for(uint i = 0;i < m_nodeNum+1;i++)
    {
        m_mustPassNodeTree[i].clear();
        m_DF[i].clear();
    }
    m_mustPassNodeTree.clear();
    m_DF.clear();
    return result;
}

template <typename  T>
void AlgorithmExecutor<T>::computeDF(uint node)
{
    for(uint i = 0;i < m_forwardGraphSize[node];i++)
    {
        uint succ = m_forwardGraph[node][i];
        if(succ == m_nodeNum+1)continue;
        if(m_idomVector[succ] != m_nodeNum+1 && m_idomVector[succ] != node)
        {
            m_DF[node].insert(succ);
        }
    }
    for(uint i = 0;i < m_mustPassNodeTree[node].size();i++)
    {
        uint son = m_mustPassNodeTree[node][i];
        computeDF(son);
        for(unordered_set<uint>::iterator it = m_DF[son].begin(); it != m_DF[son].end(); ++it)
        {
            uint mustPassSon = *it;
            uint mustPassSonCopy = mustPassSon;
            bool mustPassFlag = false;
            if(node == mustPassSon)
            {
                m_DF[node].insert(mustPassSon);
                continue;
            }
            while(m_idomVector[mustPassSonCopy] != m_nodeNum+1)
            {
                if(m_idomVector[mustPassSonCopy] == node)
                {
                    mustPassFlag = true;
                    break;
                }
                mustPassSonCopy = m_idomVector[mustPassSonCopy];
            }
            if(mustPassFlag == false)m_DF[node].insert(mustPassSon);
        }
    }
    
}
template <typename  T>
vector<vector<uint>> AlgorithmExecutor<T>::calculPhiNode(vector<vector<uint>>& Defs,vector<vector<uint>>& DF)
{
   
    uint blockNum = DF[0].size();
    uint varNum = Defs.size();

    bool* flagArr = new bool[blockNum];
    uint *flagIndexArr = new uint[blockNum];
    uint flagindexArrSize = 0;
    
    bool *DefsFlagArr = new bool [blockNum];
    uint *DefsFlagIndexArr = new uint[blockNum];
    uint DefsFlagIndexArrSize = 0;
    for(uint i = 0;i < blockNum;i++)flagArr[i] = false;
    for(uint i = 0;i < blockNum;i++)DefsFlagArr[i] = false;

    uint *w = new uint[blockNum];
    uint wSize = 0;

    vector<vector<uint>> result;
    result.resize(Defs.size());
    for(uint i = 0;i < varNum;i++)
    {
        
        for(uint j = 0; j < Defs[i].size();j++)
        {
            uint node = Defs[i][j];
            w[wSize++] = node;
            DefsFlagArr[node] = true;
            DefsFlagIndexArr[DefsFlagIndexArrSize++] = node;
        }            
        while(wSize != 0)
        {
            uint x = w[wSize-1];
            wSize--;
            for(uint j = 0;j < DF[x+1].size();j++)
            {
                uint y = DF[x+1][j];
                if (flagArr[y] == false)
                {
                    result[i].push_back(y);
                    flagIndexArr[flagindexArrSize++] = y;
                    flagArr[y] = true;
                    if(DefsFlagArr[y] == false)
                    {
                        DefsFlagIndexArr[DefsFlagIndexArrSize++] = y;
                        DefsFlagArr[y] = true;
                         w[wSize++] = y;
                    }
                }
            }
        }
        for(uint i = 0;i < flagindexArrSize;i++)
            flagArr[flagIndexArr[i]] = false;
        for(uint i = 0;i < DefsFlagIndexArrSize;i++)
            DefsFlagArr[DefsFlagIndexArr[i]] = false;
        flagindexArrSize = 0;
        DefsFlagIndexArrSize = 0;
    }
    delete [] flagArr;
    delete [] flagIndexArr;
    delete [] DefsFlagArr;
    delete [] DefsFlagIndexArr;
    delete [] w;
    return result;
}   

void testForDominantTreeIdom(void)
{
    AlgorithmExecutor<uint>* algorithmExecutor = new AlgorithmExecutor<uint>();
    vector<uint> result;
  
    vector<uint> m_startVector = {1,2,2,3,4,4,5,5};
    vector<uint> m_endVector = {2,3,4,5,5,6,2,6}; 
    result = algorithmExecutor->getDominantTreeIdom(m_startVector,m_endVector);
    
    for(uint j = 0;j < result.size()/2;j++)
    {
        cout << result[2*j] << ":" << result[2*j+1] << endl;
    }
    cout << endl;    
}


void testForUnreachableNodeList(void)
{
    AlgorithmExecutor<uint>* algorithmExecutor = new AlgorithmExecutor<uint>();
    vector<uint> result;
    vector<uint> m_startVector = {1,2,3,2,4,4,5,8,9,9,10,5,7,11,10,4,6,13,15};
    vector<uint> m_endVector = {2,3,2,4,2,5,8,9,8,10,5,7,11,12,12,6,7,14,16};
    result = algorithmExecutor->getUnreachableNodeList(m_startVector,m_endVector,1);  
    if(result.size() == 0)cout << "it is all tong!" << endl;
    else
    {
        for(uint i = 0;i < result.size();i++)
        {
            cout << result[i] << endl;
        }
    }  
}


void testForDominantFrontier(void)
{
    AlgorithmExecutor<uint>* algorithmExecutor = new AlgorithmExecutor<uint>();
    vector<vector<uint>> result;
    vector<uint> m_startVector = {1,2,2,3,4,4,5,5};
    vector<uint> m_endVector = {2,3,4,5,5,6,2,6}; 
    result = algorithmExecutor->getDominantFrontier(m_startVector,m_endVector);  
    for(uint i = 0;i < result.size();i++)
    {
        for(uint j = 0;j < result[i].size();j++)
        {
            cout << result[i][j] << "\t";
        }
        cout << endl;
    }
}

void testCalculPhiNode(void)
{
    vector<vector<uint>> DF = {{0,1,2,3,4,5},{},{1},{4},{4,5},{5,1},{}};
    vector<vector<uint>> Defs = {{2,3,4},{2,3},{5}};
  
    AlgorithmExecutor<uint>* algorithmExecutor = new AlgorithmExecutor<uint>();
    vector<vector<uint>> result = algorithmExecutor->calculPhiNode(Defs,DF);
    for(uint i = 0;i < result.size();i++)
    {
        for(uint j = 0; j < result[i].size();j++)
        {
            cout << result[i][j] << "\t";
        }
        cout << endl;
    }
}

static AlgorithmExecutor<uint>* s_algorithmExecutor = 
    AlgorithmExecutor<uint>::createAlgorithmExecutor();

#endif
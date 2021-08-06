
#ifndef LOOPOPTIMIZER_HPP
#define LOOPOPTIMIZER_HPP
#include <queue>
#include "globalPolicyExecutor.hpp"

class Loop
{
private:
    int m_id;               
    int m_head;            
    int m_newNode;         
    int m_fatherId;       
	vector<uint> m_sonLoop; 
    vector<uint> m_nodeList;
public:
    Loop();
    ~Loop(){}
    void setId(int id){m_id = id;}
    void setHeadNode(int head){m_head = head;}
    void setNewNode(int newNode){m_newNode = newNode;}
    void setFatherLoop(int fatherId){m_fatherId = fatherId;}
    void addSonLoop(uint sonId){m_sonLoop.push_back(sonId);}
    void setNodeList(vector<uint>& nodeList);
    int getId(void){return m_id;}
    int getHeadNode(void){return m_head;}
    int getNewNode(void){return m_newNode;}
    int getFatherLoop(void){return m_fatherId;}
    vector<uint>& getSonLoop(void){return m_sonLoop;}
    vector<uint>& getNodeList(void){return m_nodeList;}
};
Loop::Loop()
{
    m_id = -1;               
    m_head = -1;             
    m_newNode = -1;          
    m_fatherId = -1;         
	m_sonLoop.clear();  
    m_nodeList.clear();
}
void Loop::setNodeList(vector<uint>& nodeList)
{
    m_nodeList.clear();
    for(uint i = 0;i < nodeList.size();i++)
        m_nodeList.push_back(nodeList[i]);
}

class ArrayDirtyUnit
{
private:
    unordered_set<uint> m_dirtyIndex;
    bool m_dirtyFlag;               
public:
    void makeDirty(void){m_dirtyFlag = true;}
    void makeDirty(SsaSymb* varSymb)
    {
        if(m_dirtyFlag == true)return;
        if(varSymb == NULL)return;
        if(varSymb->type != SYM_INT)
            m_dirtyFlag = true;
        else
        {
            uint dirtyIndex = varSymb->value;
            m_dirtyIndex.insert(dirtyIndex);
        }
        
    }
    bool isDirty(SsaSymb* varSymb)
    {   
        if(varSymb == NULL)exit(-1);
        if(m_dirtyFlag == true)return true;
        if(varSymb->type == SYM_INT)
            return isDirty(varSymb->value);
        return m_dirtyFlag;         
    }
    bool isDirty(uint index)
    {
        if(m_dirtyFlag == true)return true;
        else
        {
            unordered_set<uint>::iterator it;
            it = m_dirtyIndex.find(index);
            if(it != m_dirtyIndex.end())return true;
            return false;                    
        }
    }
    ArrayDirtyUnit(void):m_dirtyFlag(false){m_dirtyIndex.clear();};
    ~ArrayDirtyUnit(void){};
};



class LoopOptimizer:
public GlobalPolicyExecutor
{
private:
    bool m_isOptimize;                     
    FunctionBlock* m_block;                 
    vector<pair<uint,uint>> m_extraEdgeList;
    vector<vector<uint>> m_mustPassNodeTree;
    vector<uint> m_idomVector;             
    vector<Loop*> m_loopList;               
    vector<bool> m_isAddNewNodeForId;      
    unordered_map<string,ArrayDirtyUnit*> m_arrAssignUnit;  
    bool m_globalArrDirtyFlag;
private: 
    void clear();
    void calMustPassNodeTree(void);         
    void calNeedCheckEdgeList(void);       
    void lookForLoop(void);               
    void buildLoopTreeBaseOnVector
        (vector<vector<uint>> &loopList);   
    void addNewNodeForALoop(uint loopId);  
    void fixTheNodeHeadForLoop(void);      
    void extraVarForALoop(uint loopId);    
    void extraVarForLoop(void);            
    bool isLoopInvariant(SsaSymb* varSymb,
    unordered_set<uint>& loopNodeSet);      
    bool isLegitDefVar(SsaSymb* varSymb);   
    bool ifarr_rCodeDirty(SsaTac* codeTac); 
    bool ifArrParameter(SsaTac* codeTac,string& varName);
    void generateArrayDirtyUnit(vector<uint>& nodeList);
    void getVarImportances(void);
public:
    LoopOptimizer();
    ~LoopOptimizer();
    void printInfoOfOptimizer(void);
    bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter);
    
};

LoopOptimizer::LoopOptimizer()
{
    clear();
    m_name = "循环优化器";
}

LoopOptimizer::~LoopOptimizer()
{
}
void LoopOptimizer::clear()
{
    m_block = NULL;
    m_isOptimize = false;
    m_globalArrDirtyFlag = false;
    m_idomVector.clear();
    m_mustPassNodeTree.clear();
    m_extraEdgeList.clear();
    m_loopList.clear();
    m_isAddNewNodeForId.clear();
    m_arrAssignUnit.clear();
}
void LoopOptimizer::printInfoOfOptimizer(void)
{
    
}
bool LoopOptimizer::runOptimizer(FunctionBlock* block,
    FuncPropertyGetter* funcPropertyGetter)
{
    clear();
    m_block = block;
    lookForLoop();              
    fixTheNodeHeadForLoop();    
    bool isOptimize = false;
    m_isOptimize = true;
    while(m_isOptimize)
    {
        m_isOptimize = false;
        extraVarForLoop();          
        if(m_isOptimize)isOptimize = true;
    }
    getVarImportances();
    return isOptimize;
}

void LoopOptimizer::calMustPassNodeTree(void)     
{
    
    vector<uint> startVector;
    vector<uint> endVector;
    startVector.clear();endVector.clear();
    m_extraEdgeList.clear();
    m_mustPassNodeTree.clear();
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    for(uint i = 0;i < forwardGraph.size();i++)
    {
        for(uint j = 0;j < forwardGraph[i].size();j++)
        {
            startVector.push_back(i);
            endVector.push_back(forwardGraph[i][j]);
        }
    }
    vector<uint> dominantTreeIdom = s_algorithmExecutor->
        getDominantTreeIdom(startVector,endVector);
    m_mustPassNodeTree.clear();
    m_mustPassNodeTree.resize(dominantTreeIdom.size()/2);
    m_idomVector.resize(dominantTreeIdom.size()/2);
    for(uint i = 0;i < m_mustPassNodeTree.size();i++)m_mustPassNodeTree[i].clear();
    for(uint i = 0;i < m_mustPassNodeTree.size();i++)
    {
        uint idomNode = dominantTreeIdom[i*2+1];
        uint sonNode = dominantTreeIdom[i*2];
        m_idomVector[sonNode] = idomNode;
        if(idomNode==sonNode)continue;
        m_mustPassNodeTree[idomNode].push_back(sonNode);
    }
    
}


void LoopOptimizer::calNeedCheckEdgeList(void)
{
    m_extraEdgeList.clear();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    vector<pair<uint,uint>> graghEdgeList;
    vector<pair<uint,uint>> mustPassEdgeList;
    graghEdgeList.clear();
    mustPassEdgeList.clear();
    for(uint i = 0;i < forwardGraph.size();i++)
    {
        for(uint j = 0;j < forwardGraph[i].size();j++)
            graghEdgeList.push_back(make_pair(i,forwardGraph[i][j]));
    }
    m_extraEdgeList.resize(graghEdgeList.size());
    for(uint i = 1;i < m_idomVector.size();i++)
    {
        uint endPoint = i;
        uint startPoint = m_idomVector[i];
        mustPassEdgeList.push_back(make_pair(startPoint,endPoint));
    }
    sort(graghEdgeList.begin(),graghEdgeList.end());
    sort(mustPassEdgeList.begin(),mustPassEdgeList.end());
    vector<pair<uint,uint>>::iterator it = 
    set_difference(graghEdgeList.begin(), graghEdgeList.end(), 
    mustPassEdgeList.begin(), mustPassEdgeList.end(), m_extraEdgeList.begin());
    m_extraEdgeList.resize(it - m_extraEdgeList.begin()); 
}

void LoopOptimizer::lookForLoop(void)             
{
  
    calMustPassNodeTree();
    
    calNeedCheckEdgeList();
    
    vector<vector<uint>> loopList;				    
    loopList.clear();
    for(uint i = 0;i < m_extraEdgeList.size();i++)
    {
        vector<uint> newVector;
        newVector.clear();
        uint startPoint = m_extraEdgeList[i].first;
        uint endPoint = m_extraEdgeList[i].second;
        do
        {
            newVector.push_back(startPoint);
            if(m_idomVector[startPoint] == 0 ||
            m_idomVector[startPoint] == endPoint)break;
            startPoint = m_idomVector[startPoint];
        }while(1);
        if(m_idomVector[startPoint] == 0)continue; 
      
        newVector.clear();
        newVector.push_back(m_extraEdgeList[i].second);
        newVector.push_back(m_extraEdgeList[i].first);
        loopList.push_back(newVector);
    }
    
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    vector<unordered_set<uint>> loopNodeListSet;
    loopNodeListSet.clear();
    loopNodeListSet.resize(loopList.size());
    for(uint i = 0;i < loopList.size();i++)
    {
        uint headNode = loopList[i][0];
        uint startPoint = loopList[i][1];
        loopNodeListSet[i].insert(headNode);
        loopNodeListSet[i].insert(startPoint);
        
        queue<uint> prevList;
        prevList.push(startPoint);
        while(!prevList.empty())
        {
            uint needToLookNode = prevList.front();
            prevList.pop();       
            for(uint j = 0;j < backwardGraph[needToLookNode].size();j++)
            {
                uint prevBid = backwardGraph[needToLookNode][j];
                if(prevBid != headNode && loopNodeListSet[i].find(prevBid)
                     == loopNodeListSet[i].end())
                {
                    prevList.push(prevBid);
                    loopNodeListSet[i].insert(prevBid);
                    loopList[i].push_back(prevBid);
                }
            }
        }
    }
    buildLoopTreeBaseOnVector(loopList);
}

void LoopOptimizer::buildLoopTreeBaseOnVector(vector<vector<uint>> &loopList)
{
    m_loopList.clear();
    for(uint i = 0;i < loopList.size();i++)
    {
        Loop* newLoop = new Loop();
        newLoop->setId(i);
        newLoop->setHeadNode(loopList[i][0]);
        newLoop->setNodeList(loopList[i]);
        m_loopList.push_back(newLoop);
    }
   
    uint loopNum = m_loopList.size();
    vector<unordered_set<uint>> loopNodeSetList;
    loopNodeSetList.resize(loopNum);
    for(uint i = 0;i < loopNum;i++)
    {
        vector<uint>& nodeListTemp = m_loopList[i]->getNodeList();
        for(uint j = 0;j < nodeListTemp.size();j++)
            loopNodeSetList[i].insert(nodeListTemp[j]);
    }
    vector<vector<uint>> youngerOfId;
    vector<uint> inDegreeOfId;
    youngerOfId.resize(loopNum);
    inDegreeOfId.resize(loopNum);
    for(uint i = 0;i < loopNum;i++)youngerOfId[i].clear();
    for(uint i = 0;i < loopNum;i++)inDegreeOfId[i] = 0;
    for(uint i = 0;i < loopNum;i++)
    {
        int headNode = m_loopList[i]->getHeadNode();
        for(uint j = 0;j < loopNum;j++)
        {
            if(j == i)continue;
            if(loopNodeSetList[j].find(headNode)
            == loopNodeSetList[j].end())continue;
         
            youngerOfId[j].push_back(i);
            inDegreeOfId[i]++;         
        }
    }
    
    queue<uint> canFindFatherNode;
    while(!canFindFatherNode.empty())canFindFatherNode.pop();
    for(uint i = 0;i < inDegreeOfId.size();i++)
    {
        if(inDegreeOfId[i] != 0)continue;
        canFindFatherNode.push(i);
    }
    while(!canFindFatherNode.empty())
    {
        uint headNode = canFindFatherNode.front();
        canFindFatherNode.pop();
        for(uint i = 0;i < youngerOfId[headNode].size();i++)
        {
            uint youngerOfNode = youngerOfId[headNode][i];
            inDegreeOfId[youngerOfNode]--;
            if(inDegreeOfId[youngerOfNode] != 0)continue;
         
            canFindFatherNode.push(youngerOfNode);
            
            m_loopList[youngerOfNode]->setFatherLoop(headNode);
            m_loopList[headNode]->addSonLoop(youngerOfNode);
        }
    }
}

void LoopOptimizer::fixTheNodeHeadForLoop(void)   
{

    m_isAddNewNodeForId.resize(m_loopList.size());
    for(uint i = 0;i < m_isAddNewNodeForId.size();i++)
        m_isAddNewNodeForId[i] = false;
    for(uint i = 0;i < m_loopList.size();i++)
    {
        if(m_isAddNewNodeForId[i])continue;
        addNewNodeForALoop(i);            
    }
}

void LoopOptimizer::addNewNodeForALoop(uint loopId)
{
    m_isAddNewNodeForId[loopId] = true;
    vector<uint> &sonLoop = m_loopList[loopId]->getSonLoop();
    for(uint i = 0;i < sonLoop.size();i++)
        addNewNodeForALoop(sonLoop[i]);
   
    unordered_set<uint> loopNodeSet;
    vector<uint> extraPrevBidList;
    loopNodeSet.clear();
    extraPrevBidList.clear();
    vector<uint>& nodeList = m_loopList[loopId]->getNodeList();
    for(uint i = 0;i < nodeList.size();i++)loopNodeSet.insert(nodeList[i]);
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    uint headNode = m_loopList[loopId]->getHeadNode();
    int FatherLoopId = m_loopList[loopId]->getFatherLoop();
    for(uint i = 0;i < backwardGraph[headNode].size();i++)
    {
        uint prevBid = backwardGraph[headNode][i];
        if(loopNodeSet.find(prevBid) != loopNodeSet.end())continue;
        extraPrevBidList.push_back(prevBid);
    }
    
    if(extraPrevBidList.size() == 0)exit(-1);
    do
    {
        int headNodeOfFatherLoop; 
        if(FatherLoopId == -1)headNodeOfFatherLoop = -1;
        else headNodeOfFatherLoop = m_loopList[FatherLoopId]->getHeadNode();
        if(extraPrevBidList.size() != 1)continue;
        uint node = extraPrevBidList[0];
        if(forwardGraph[node].size() != 1)continue;
        if(node == headNodeOfFatherLoop)continue;
        
        m_loopList[loopId]->setNewNode(node);
        return;
    } while (0);
    
    uint newNode = m_block->addNewNodeForLoop(headNode,extraPrevBidList);
    m_loopList[loopId]->setNewNode(newNode);
    while(FatherLoopId != -1)
    {
        vector<uint>& fatherLoopNode = m_loopList[FatherLoopId]->getNodeList();
        vector<uint>::iterator it = find(fatherLoopNode.begin(),fatherLoopNode.end(),headNode);
        if(it == fatherLoopNode.end())break;
        fatherLoopNode.insert(it,newNode);
        FatherLoopId = m_loopList[FatherLoopId]->getFatherLoop();
    }
}

void LoopOptimizer::extraVarForLoop(void)         
{
    
    m_isAddNewNodeForId.clear();
    m_isAddNewNodeForId.resize(m_loopList.size());
    for(uint i = 0;i < m_isAddNewNodeForId.size();i++)
        m_isAddNewNodeForId[i] = false;
    for(uint i = 0;i < m_loopList.size();i++)
    {
        if(m_isAddNewNodeForId[i])continue;
        extraVarForALoop(i);               
    }
}

void LoopOptimizer::extraVarForALoop(uint loopId)
{
    m_isAddNewNodeForId[loopId] = true;
    vector<uint> &sonLoop = m_loopList[loopId]->getSonLoop();
    for(uint i = 0;i < sonLoop.size();i++)
        extraVarForALoop(sonLoop[i]);
    
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<SsaTac*> needExtractTacs;
    vector<uint> needExtractTacsType;
    unordered_set<uint> loopNodeSet;
    loopNodeSet.clear();
    needExtractTacs.clear();
    needExtractTacsType.clear();
    vector<uint>& nodeList = m_loopList[loopId]->getNodeList();
    for(uint i = 0;i < nodeList.size();i++)loopNodeSet.insert(nodeList[i]);
    uint newNode = m_loopList[loopId]->getNewNode();
    generateArrayDirtyUnit(nodeList);
    for(uint i = 0;i < nodeList.size();i++)  
    {
        uint blockId = nodeList[i];
        SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
        SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        tacHead->prev = tacHeadHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
            switch (curTac->type)
            {
            case TAC_ADD:
            case TAC_SUB:
            case TAC_MUL:
            case TAC_DIV:
            case TAC_EQ:
            case TAC_MOD:
            case TAC_NE:
            case TAC_LT:
            case TAC_LE:
            case TAC_GT:
            case TAC_GE:
            case TAC_OR:
            case TAC_AND:
                if(!isLegitDefVar(curTac->first))break;
                if(!isLoopInvariant(curTac->second,loopNodeSet))break;
                if(!isLoopInvariant(curTac->third,loopNodeSet))break;
                m_isOptimize = true;
                curTac->blockId = newNode;
                needExtractTacsType.push_back(curTac->type);
                curTac->type = TAC_UNDEF;
                needExtractTacs.push_back(curTac);
                break;
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY:
                if(!isLegitDefVar(curTac->first))break;
                if(!isLoopInvariant(curTac->second,loopNodeSet))break;
                m_isOptimize = true;
                curTac->blockId = newNode;
                needExtractTacsType.push_back(curTac->type);
                curTac->type = TAC_UNDEF;
                needExtractTacs.push_back(curTac);                
                break;
            case TAC_LEA:
                if(!isLegitDefVar(curTac->first))break;
                if(!isLoopInvariant(curTac->third,loopNodeSet))break;
                m_isOptimize = true;
                curTac->blockId = newNode;
                needExtractTacsType.push_back(curTac->type);
                curTac->type = TAC_UNDEF;
                needExtractTacs.push_back(curTac);   
                break;
            case TAC_ARR_R:
                if(!isLegitDefVar(curTac->first))break;
                if(!isLoopInvariant(curTac->third,loopNodeSet))break;
                if(m_globalArrDirtyFlag == true &&
                    curTac->second->name[0] == 'g')break;
                if(ifarr_rCodeDirty(curTac))break;
                m_isOptimize = true;
                curTac->blockId = newNode;
                needExtractTacsType.push_back(curTac->type);
                
                curTac->type = TAC_UNDEF;
                needExtractTacs.push_back(curTac);  
                
                break;
            
            default:
                break;
            }
        } while (curTac != tacTail);
        delete tacHeadHead;
    }
    for(uint i = 0;i < nodeList.size();i++)
    {
        uint blockId = nodeList[i];
        basicBlocks[blockId]->raiseUnUseTac();
    }
    for(uint i = 0;i < needExtractTacs.size();i++)
    {
        needExtractTacs[i]->type = needExtractTacsType[i];
        basicBlocks[newNode]->insertTacToTail(needExtractTacs[i]);
    }
}

bool LoopOptimizer::isLoopInvariant(SsaSymb* 
    varSymb,unordered_set<uint>& loopNodeSet)
{
    if(varSymb->type == SYM_INT)return true;
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    if(uName2SsaSymbs.find(varSymb->name) == uName2SsaSymbs.end() &&
    tName2SsaSymbs.find(varSymb->name) == tName2SsaSymbs.end())return false;
    uint defBlockId = varSymb->defPoint->blockId;
    if(loopNodeSet.find(defBlockId) == loopNodeSet.end())return true;
    return false;
}

bool LoopOptimizer::isLegitDefVar(SsaSymb* varSymb)   
{
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    if(uName2SsaSymbs.find(varSymb->name) == uName2SsaSymbs.end() &&
    tName2SsaSymbs.find(varSymb->name) == tName2SsaSymbs.end())return false;
    return true;
}


void LoopOptimizer::generateArrayDirtyUnit(vector<uint>& nodeList)
{
    m_arrAssignUnit.clear();
    m_globalArrDirtyFlag = false;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    for(uint i = 0;i < nodeList.size();i++)
    {
        uint blockId = nodeList[i];
        SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
        SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead; 
        do
        {
            curTac = curTac->next;
            switch(curTac->type)
            {
                case TAC_ARR_L:
                    {
                        ArrayDirtyUnit* curArr;
                        unordered_map<string,ArrayDirtyUnit*>::iterator it;
                        it = m_arrAssignUnit.find(curTac->first->name);
                        if(it == m_arrAssignUnit.end())
                        {
                            curArr = new ArrayDirtyUnit();
                            m_arrAssignUnit[curTac->first->name] = curArr;
                        }
                        else curArr = it->second;
                        curArr->makeDirty(curTac->second);
                    }
                    break;
                case TAC_ACTUAL:
                    {
                        string parameterName;
                        if(!ifArrParameter(curTac,parameterName))break;
                        ArrayDirtyUnit* curArr;
                        unordered_map<string,ArrayDirtyUnit*>::iterator it;
                        it = m_arrAssignUnit.find(parameterName);
                        if(it == m_arrAssignUnit.end())
                        {
                            curArr = new ArrayDirtyUnit();
                            m_arrAssignUnit[parameterName] = curArr;
                        }  
                        else curArr = it->second;   
                        curArr->makeDirty();                   
                    }
                case TAC_CALL:
                    {
                        m_globalArrDirtyFlag = true;
                    }
                    break;
            }
        }while(curTac != tacTail);
    }
}

bool LoopOptimizer::ifarr_rCodeDirty(SsaTac* codeTac)
{
    if(m_arrAssignUnit.empty())return false;
    unordered_map<string,ArrayDirtyUnit*>::iterator it;
    it = m_arrAssignUnit.find(codeTac->second->name);
    if(it == m_arrAssignUnit.end())return false;
    else
    {
        return m_arrAssignUnit[codeTac->second->name]
            ->isDirty(codeTac->third);
    }
}

bool LoopOptimizer::ifArrParameter(SsaTac* codeTac,string& varName)
{
    if(codeTac->type != TAC_ACTUAL)exit(-1);
    if(codeTac->first->type == SYM_INT)return false;
    if(codeTac->first->name[0] =='g')return false;
    SsaSymb* needToJudge = codeTac->first;
    do
    {
        SsaTac* defTac = needToJudge->defPoint;
        if(defTac->type == TAC_COPY)
        {
            if(defTac->second->type == SYM_INT)return false;
            if(defTac->second->type == SYM_VAR &&
                defTac->second->name[0] == 'g')return false;
            needToJudge = defTac->second;
        }
        else if(defTac->type == TAC_LEA)
        {
            varName = defTac->second->name;
            return true;
        }
        else return false;
    }while(1);
}

void LoopOptimizer::getVarImportances(void)
{
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    for(uint i = 0;i < basicBlocks.size();i++)
    {
        SsaTac* tacHead = basicBlocks[i]->getTacHead();
        SsaTac* tacTail = basicBlocks[i]->getTacTail();
        if(tacHead == NULL)continue;  
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead; 
        do
        {
            curTac = curTac->next;
            
            curTac->priority = 0;
        }while(curTac != tacTail);
        delete tacHeadHead;
    }
    for(uint i = 0;i < m_loopList.size();i++)
    {
        vector<uint>& nodeList = m_loopList[i]->getNodeList();
        for(uint j = 0;j < nodeList.size();j++)
        {
            uint blockId = nodeList[j];
            SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
            SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
            if(tacHead == NULL)continue;  
            SsaTac* tacHeadHead = new SsaTac();
            tacHeadHead->next = tacHead;
            SsaTac* curTac = tacHeadHead; 
            do
            {
                curTac = curTac->next;
                if(curTac->type == TAC_LABEL)continue;
                else if(curTac->type == TAC_FORMAL)continue;
                else if(curTac->type == TAC_GOTO)continue;
                curTac->priority++;
            }while(curTac != tacTail);
            delete tacHeadHead;
        }
    }
}

#endif
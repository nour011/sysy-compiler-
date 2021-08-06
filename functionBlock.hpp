#ifndef FUNCTIONBLOCK_HPP
#define FUNCTIONBLOCK_HPP
#include <unordered_map>
#include <iostream>
#include <algorithm>
#include "basicBlock.hpp"
#include "frontEndInput.hpp"
#include "ssaCodeStruct.hpp"
#include "globalSymTable.hpp"
#include "funcSymTable.hpp"
#include "blockSymTable.hpp"
#include "algorithmExecutor.hpp"
using namespace std;
typedef unsigned int uint;
#define SSAMODE true
#define COMMODE false

class FunctionBlock
{
private:
public:
    
    string m_name;                                              
    vector<BasicBlock*> m_basicBlocks;                          
    vector<vector<uint>> m_forwardGraph;                        
    vector<vector<uint>> m_backwardGraph;                       
    FuncSymTable* m_funcSymTable;                               
    static GlobalSymTable* s_globalSymTable;                    
    vector<BlockSymTable*> m_blockSymTables;                    
    unordered_map<string,SsaSymb*> m_uName2SsaSymbs;           
    unordered_map<string,SsaSymb*> m_tName2SsaSymbs;            
private:
    vector<uint> calcBasicBlockPartPoints
        (SsaTac* beginTac,map<uint,uint>& tableOfLid2Bid);     
    void divideBasicBlockBaseOnPoints(SsaTac* beginTac,
    vector<uint>& dividePoints,map<uint,uint>& tableOfLid2Bid);
    void buildControlFlowGraph(void);                          
    void deleteUnreachableBlock(void);                         
    void directDeleteBasicBlock(vector<uint> BidList);          
    void deleteBasicBlockPrevWork(vector<uint> BidList);        
    void cleanVarInfluence(vector<uint> BidList);               
    uint getBlockPrintSucc(uint blockId);                      
    uint getBlockPrintPrev(uint blockId);                      
    void addBasicBlockPreWork(void);                            
    void edgeSegmentation(void);                               
    void getEdgeNeedToSegmentation(vector<uint>& 
        needSegStartPoints,vector<uint>& needSegEndPoints);     
    uint getMaxDNumOfUVar(string varName);                      
public:
    FunctionBlock();
    ~FunctionBlock(){};
    static GlobalSymTable* createGlobalSymTable(void);          
    void buildBlockFromTacs(SsaTac* tacHead);                  

  
    void cleanDirtySsaTac(void);                                
    void deleteBasicBlock(vector<uint> BidList);               
    uint addNewNodeForLoop(uint loopHead,vector<uint> prevBids);
    void deleteExtraGotoBlocks(void);                           

    void printFunctionBlock(void);                              
    void printFunctionBlockDirct(void);
    void printControlFlowGraph(void);
    void printBasicBlockNum(void);
    vector<vector<uint>> getPrintList(void);                  
    
    
    uint getTheLineOfFunction(void);            
    vector<BasicBlock*>& getBasicBlocks(void){return m_basicBlocks;}
    FuncSymTable*& getFuncSymTable(void){return m_funcSymTable;}
    unordered_map<string,SsaSymb*>& getUName2SsaSymbs(void){return m_uName2SsaSymbs;}
    unordered_map<string,SsaSymb*>& getTName2SsaSymbs(void){return m_tName2SsaSymbs;}
    vector<vector<uint>>& getForwardGraph(void){return m_forwardGraph;};
    vector<vector<uint>>& getBackwardGraph(void){return m_backwardGraph;};
    
};

GlobalSymTable* FunctionBlock::s_globalSymTable = FunctionBlock::createGlobalSymTable();



FunctionBlock::FunctionBlock()
{
    m_name.clear();
    m_funcSymTable = NULL;
    m_blockSymTables.clear();
    m_basicBlocks.clear();
    m_forwardGraph.clear();
    m_backwardGraph.clear();
    m_uName2SsaSymbs.clear();
    m_tName2SsaSymbs.clear(); 
}
uint FunctionBlock::getTheLineOfFunction(void)
{
    uint lineNum = 0;
    for(uint i = 0;i < m_basicBlocks.size();i++)
        lineNum += m_basicBlocks[i]->m_instNum;
    return lineNum;
}

GlobalSymTable* FunctionBlock::createGlobalSymTable(void)
{
    GlobalSymTable* m_globalSymTable = new GlobalSymTable();
    return m_globalSymTable;
}

void FunctionBlock::printFunctionBlockDirct(void)
{
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        m_basicBlocks[i]->printBasicBlock();
    }
}

vector<uint> FunctionBlock::calcBasicBlockPartPoints
    (SsaTac* beginTac,map<uint,uint>& tableOfLid2Bid)
{
    vector<uint> dividePoints;                                  
    uint curDividePoint = 0;
    tableOfLid2Bid.clear();
    dividePoints.clear();
    dividePoints.push_back(curDividePoint);
    for(SsaTac* curTac = beginTac;curTac->next != NULL;
            curTac = curTac->next)
    {
        curDividePoint++;
        
        switch(curTac->next->type)
        {
        case TAC_GOTO:
            dividePoints.push_back(curDividePoint);
            break;
        case TAC_IFZ:
            dividePoints.push_back(curDividePoint);
            break;
        case TAC_RETURN:
            dividePoints.push_back(curDividePoint);
            break;
        case TAC_ENDFUNC:
            if(dividePoints.back() != curDividePoint-1)
                dividePoints.push_back(curDividePoint-1);
            break;
        case TAC_LABEL:
            {
                if(dividePoints.back() != curDividePoint-1)
                    dividePoints.push_back(curDividePoint-1);
                char* name = curTac->next->first->name;
                int idLNumber = atoi(name+1);
                int idBNumber = dividePoints.size();                
                tableOfLid2Bid[idLNumber] = idBNumber;
            }
            break;
        case TAC_CALL:
            {
                if(dividePoints.back() != curDividePoint-1)
                    dividePoints.push_back(curDividePoint-1); 
                dividePoints.push_back(curDividePoint);
            }
            break;
        default:
            break; 
        }
        if(curTac->next->type == TAC_ENDFUNC)break;
    }
    return dividePoints;    
}

void FunctionBlock::divideBasicBlockBaseOnPoints(SsaTac* beginTac,
    vector<uint>& dividePoints,map<uint,uint>& tableOfLid2Bid)
{
    SsaTac* curTac = beginTac;
    for(uint idOfB = 0;idOfB < dividePoints.size()-1;idOfB++)
    {
        int instNum = dividePoints[idOfB+1]-dividePoints[idOfB];
        SsaTac* blockTacHead = curTac->next;
        SsaTac* blockTacTail = blockTacHead;
        BasicBlock* curbBlock = new BasicBlock();
        curbBlock->setinstNum(instNum);
        while(instNum--)
        {
            if(blockTacTail->type == TAC_IFZ)
            {
                char* name = blockTacTail->second->name;
                int Bid = tableOfLid2Bid[atoi(name+1)];
                sprintf(blockTacTail->second->name,"B%d",Bid);
            }
            else if(blockTacTail->type == TAC_GOTO
                || blockTacTail->type == TAC_LABEL)
            {
                char* name = blockTacTail->first->name;
                int Bid = tableOfLid2Bid[atoi(name+1)];
                sprintf(blockTacTail->first->name,"B%d",Bid);
            }
            if(instNum != 0)
            blockTacTail = blockTacTail->next;
        }
        curbBlock->setTacHead(blockTacHead);
        curbBlock->setTacTail(blockTacTail);
        curbBlock->setId(idOfB+1);
        m_basicBlocks.push_back(curbBlock);
        curTac = blockTacTail;
    }
}

void FunctionBlock::buildBlockFromTacs(SsaTac* tacHead)
{
    m_name.clear();
    m_name.append(tacHead->next->first->name);
    SsaTac* curTac = tacHead->next->next;
    SsaTac* beginTac = curTac;
   
    m_funcSymTable = new FuncSymTable();
    for(;curTac->next != NULL;curTac = curTac->next)
    {
        if(curTac->next->type != TAC_VAR &&
            curTac->next->type != TAC_ARR &&
            curTac->next->type != TAC_FORMAL)break;
        if(curTac->next->type == TAC_ARR)
            m_funcSymTable->addArrTac(curTac->next);
        if(curTac->next->first->name[0] == 'u')
            m_funcSymTable->addVar(curTac->next->first);
    }
   
    if(curTac->next->type == TAC_ENDFUNC)return;
    
   
    
    SsaTac* formalEndTac = beginTac;
    while(formalEndTac->next->type == TAC_FORMAL)
        formalEndTac = formalEndTac->next;
    
    SsaTac* defHead = curTac->next;
    formalEndTac->next = defHead;
    defHead->prev = formalEndTac;
    map<uint,uint> tableOfLid2Bid;
    vector<uint> dividePoints = 
        calcBasicBlockPartPoints(beginTac,tableOfLid2Bid);
  
    BasicBlock *extryBlock = new BasicBlock();
    extryBlock->setId(0);
    extryBlock->setinstNum(0);
    extryBlock->setTacHead(NULL);
    extryBlock->setTacTail(NULL);
    m_basicBlocks.push_back(extryBlock);
    divideBasicBlockBaseOnPoints
    (beginTac,dividePoints,tableOfLid2Bid);
    BasicBlock *exitBlock = new BasicBlock();
    exitBlock->setId(dividePoints.size());
    exitBlock->setinstNum(0);
    exitBlock->setTacHead(NULL);
    exitBlock->setTacTail(NULL);
    m_basicBlocks.push_back(exitBlock);
    buildControlFlowGraph();
    deleteUnreachableBlock();
}

void FunctionBlock::buildControlFlowGraph(void)
{
    m_forwardGraph.clear();
    m_backwardGraph.clear();
    m_forwardGraph.resize(m_basicBlocks.size());
    m_backwardGraph.resize(m_basicBlocks.size());
    m_forwardGraph[0].push_back(1);
    m_backwardGraph[1].push_back(0);
    for(uint i = 1;i < m_basicBlocks.size()-1;i++)
    {
        SsaTac* tacTail = m_basicBlocks[i]->getTacTail();
        if(tacTail == NULL)continue;
        switch(tacTail->type)
        {
            case TAC_IFZ:

                {
                    m_forwardGraph[i].push_back(i+1);
                    m_backwardGraph[i+1].push_back(i);
                    char *name = tacTail->second->name;
                    uint Bid = atoi(name+1);
                    if(Bid != i+1)
                    {
                        m_forwardGraph[i].push_back(Bid);
                        m_backwardGraph[Bid].push_back(i);
                    }
                    else
                    {
                        tacTail->type = TAC_UNDEF;
                        m_basicBlocks[i]->cleanDirtyTac();
                    }
                    break;
                }
            case TAC_GOTO:
                {                
                    char *name = tacTail->first->name;
                    uint Bid = atoi(name+1);
                    m_forwardGraph[i].push_back(Bid);
                    m_backwardGraph[Bid].push_back(i); 
                    break;
                }               
            case TAC_RETURN:
                m_forwardGraph[i].push_back(m_basicBlocks.size()-1);
                m_backwardGraph[m_basicBlocks.size()-1].push_back(i);
                break;
            default:
                m_forwardGraph[i].push_back(i+1);
                m_backwardGraph[i+1].push_back(i);
                break;
        }
    }
}



void FunctionBlock::deleteUnreachableBlock(void)
{
    vector<uint> startVector;
    vector<uint> endVector;
    vector<uint> deleteBidList;
    startVector.clear();
    endVector.clear();
    for(uint i = 0;i < m_forwardGraph.size();i++)
    {
        for(uint j = 0;j < m_forwardGraph[i].size();j++)
        {
            startVector.push_back(i);
            endVector.push_back(m_forwardGraph[i][j]);
        }
    }
    deleteBidList = s_algorithmExecutor
    ->getUnreachableNodeList(startVector,endVector,0);
    if(deleteBidList.size() != 0)deleteBasicBlock(deleteBidList);
    edgeSegmentation();
}

void FunctionBlock::printFunctionBlock(void)
{
    vector<uint> printOrder;
    printOrder.clear();
    vector<vector<uint>> PrintList = getPrintList();
    for(uint i = 0; i < PrintList.size();i++)
    {
        for(uint j = 0;j < PrintList[i].size();j++)
            printOrder.push_back(PrintList[i][j]);
    }
    printOrder.push_back(m_basicBlocks.size()-1);
    cout << "@" << endl;
    cout << "label " <<  m_name << endl;
    cout << "begin"  << endl;
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        m_basicBlocks[printOrder[i]]->printBasicBlock();
    }
    cout << "end"  << endl;
}

void FunctionBlock::printBasicBlockNum(void)
{
    cout << "@" << endl;
    cout << "there have "<< m_basicBlocks.size()-2 << " blocks!" << endl;
}

void FunctionBlock::printControlFlowGraph(void)
{
    cout << "@" << endl;
    cout << "start block: start->B" << m_forwardGraph[0][0] << endl;
    for(uint i = 1;i < m_forwardGraph.size()-1;i++)
    {
        cout << "B" << i << " can reach list: ";
        for(uint j = 0;j < m_forwardGraph[i].size();j++)
        {
            if(m_forwardGraph[i][j] == m_forwardGraph.size()-1)
                cout << "end" << "\t";
            else cout << "B" << m_forwardGraph[i][j] << "\t";
        }
        cout << endl;
    }
}



void FunctionBlock::deleteBasicBlockPrevWork(vector<uint> BidList)
{
    unordered_set<uint> needCleanBid;
    needCleanBid.clear();
    
    for(uint i = 0;i < BidList.size();i++)
    {
        uint needDeleteBid = BidList[i];
        if(m_backwardGraph[needDeleteBid].size() == 0)continue;

        for(uint j = 0;j < m_backwardGraph[needDeleteBid].size();j++)
        {
            uint prevBid = m_backwardGraph[needDeleteBid][j];
            SsaTac* tacTail = m_basicBlocks[prevBid]->getTacTail();
            if(tacTail == NULL)continue;
            if(tacTail->type == TAC_GOTO)
            {
                tacTail->type = TAC_UNDEF;
                needCleanBid.insert(prevBid);
                continue;
            }
            if(tacTail->type == TAC_IFZ)
            {
                uint succOfIfzBid = getBlockPrintSucc(prevBid);
                if(succOfIfzBid != needDeleteBid)
                {
                    tacTail->type = TAC_UNDEF;
                    needCleanBid.insert(prevBid);
                    continue;
                }
              
                uint gotoBid = atoi(tacTail->second->name+1);
               
                if(gotoBid == prevBid)
                {
                    tacTail->type = TAC_GOTO;
                    tacTail->first = tacTail->second;
                    tacTail->second = NULL;
                    continue;
                }
                uint prevOfGotoBid = getBlockPrintPrev(gotoBid);
                if(prevOfGotoBid == gotoBid)
                {
                    
                    tacTail->type = TAC_UNDEF;
                    needCleanBid.insert(prevBid);
                    continue;
                }
                
                tacTail->type = TAC_GOTO;
                tacTail->first = tacTail->second;
                tacTail->second = NULL;
                continue;
            }
            
        }
    }
    unordered_set<uint>::iterator it = needCleanBid.begin();
    for(;it != needCleanBid.end();it++)
        m_basicBlocks[*it]->cleanDirtyTac();
    
    unordered_set<uint> needDeleteSet;
    needDeleteSet.clear();
    for(uint i = 0;i < BidList.size();i++)
        needDeleteSet.insert(BidList[i]);
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        if(m_backwardGraph[i].size() == 0)continue;
        if(needDeleteSet.find(i) != needDeleteSet.end())continue;

        vector<uint> needDeletePrev;
        needDeletePrev.clear();
        for(int j = m_backwardGraph[i].size()-1;j >= 0;j--)
        {
            uint prevBid = m_backwardGraph[i][j];
            if(needDeleteSet.find(prevBid) != needDeleteSet.end())
                needDeletePrev.push_back(j);
        }
        if(needDeletePrev.size() == 0)continue;
        SsaTac* tacHead = m_basicBlocks[i]->getTacHead();
        SsaTac* tacTail = m_basicBlocks[i]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
            if(curTac->type != TAC_INSERT)break;
            for(uint j = 0;j < curTac->functionSymb.size();j++)
            {
                if(curTac->functionSymb2Tac[j] == NULL)continue;
                curTac->functionSymb[j]->useTimes--;
                deleteUseSsaTac(curTac->functionSymb2Tac[j]);
            }
            for(uint j  = 0;j < needDeletePrev.size();j++)
            {
                curTac->functionSymb.erase(curTac->functionSymb.begin()+needDeletePrev[j]);
                curTac->functionSymb2Tac.erase(curTac->functionSymb2Tac.begin()+needDeletePrev[j]);
            }
            for(uint j = 0;j < curTac->functionSymb.size();j++)
            {
                if(curTac->functionSymb[j]->type == SYM_INT)continue;
                if(m_tName2SsaSymbs.find(curTac->functionSymb[j]->name) == m_tName2SsaSymbs.end() &&
                m_uName2SsaSymbs.find(curTac->functionSymb[j]->name) == m_uName2SsaSymbs.end())continue;
                addTacToUseListForSsaSymb(curTac,
                curTac->functionSymb[j],curTac->functionSymb2Tac[j]);
            }
        } while (curTac != tacTail);
        delete tacHeadHead;
    }
}

uint FunctionBlock::getBlockPrintSucc(uint blockId)
{
    uint exitBlockId = m_basicBlocks.size()-1;
    SsaTac* tacTail = m_basicBlocks[blockId]->getTacTail();
    if(tacTail != NULL && tacTail->type == TAC_GOTO)return blockId;
    if(tacTail != NULL && (tacTail->type == TAC_IFZ ||
    tacTail->type == TAC_IFEQ || tacTail->type == TAC_IFNE
    || tacTail->type == TAC_IFLT || tacTail->type == TAC_IFLE
    || tacTail->type == TAC_IFGT || tacTail->type == TAC_IFGE))
    {
        uint gotoBid = atoi(tacTail->second->name+1);
        uint firstBid = m_forwardGraph[blockId][0];
        if(firstBid != gotoBid && firstBid == exitBlockId)return blockId;
        if(firstBid != gotoBid)return firstBid;
        if(m_forwardGraph[blockId][1] == exitBlockId)return blockId;
        return m_forwardGraph[blockId][1];
    }
    uint succNum = m_forwardGraph[blockId].size();
    if(succNum == 0)return blockId;
    if(m_forwardGraph[blockId][0] == exitBlockId)return blockId;
    return m_forwardGraph[blockId][0];
}

uint FunctionBlock::getBlockPrintPrev(uint blockId)
{ 
    if(m_backwardGraph[blockId].size() == 0)return blockId;
    for(uint i = 0;i < m_backwardGraph[blockId].size();i++)
    {
        uint succBid = m_backwardGraph[blockId][i];
        SsaTac* tacTail = m_basicBlocks[succBid]->getTacTail();
        if(tacTail == NULL)return succBid;
        if(tacTail->type == TAC_GOTO)continue;
        if(tacTail->type == TAC_IFZ||
        tacTail->type == TAC_IFEQ || tacTail->type == TAC_IFNE
        || tacTail->type == TAC_IFLT || tacTail->type == TAC_IFLE
        || tacTail->type == TAC_IFGT || tacTail->type == TAC_IFGE)
        {
            uint gotoBid = atoi(tacTail->second->name+1);
            if(gotoBid == blockId)continue;
            return succBid;
        }
        return succBid;
    }
    return blockId;
}

vector<vector<uint>> FunctionBlock::getPrintList(void)
{
    vector<vector<uint>> pointRoadList;
    uint blockNum = m_basicBlocks.size();
    bool *pointPrintFlag = new bool[blockNum];
    for(uint i=0;i<blockNum;i++)pointPrintFlag[i] = false;
    pointPrintFlag[blockNum-1] = true;
    pointRoadList.clear();
    for(uint i = 0;i < blockNum-1;i++)
    {
        uint prevNode = i;
        if(pointPrintFlag[prevNode] == true)continue;
        while (prevNode != getBlockPrintPrev(prevNode))
            prevNode = getBlockPrintPrev(prevNode);
        uint succNode = prevNode;
        vector<uint> pointRoad;
        pointRoad.clear();
        while(succNode != getBlockPrintSucc(succNode))
        {
            pointRoad.push_back(succNode);
            pointPrintFlag[succNode] = true;
            succNode = getBlockPrintSucc(succNode);
        }
        pointRoad.push_back(succNode);
        pointPrintFlag[succNode] = true;
        pointRoadList.push_back(pointRoad);
    }
    return pointRoadList;
}
void FunctionBlock::directDeleteBasicBlock(vector<uint> BidList)
{
    uint blockNum = m_basicBlocks.size();
    uint deleteNum = BidList.size();
    bool* BidFlag = new bool[blockNum];
    uint* old2new = new uint[blockNum];
    vector<uint> BidSortList(0);
    for(uint i = 0; i < blockNum;i++)BidFlag[i] = true;
    for(uint i = 0; i < BidList.size();i++)BidFlag[BidList[i]] =false;
    for(uint i = 0,cnt = 0;i < blockNum;i++)
    {
        old2new[i] = cnt;
        if(BidFlag[i] == true)cnt++;
        else BidSortList.push_back(i);
    }    
    for(int i = BidSortList.size()-1;i>=0;i--)
        m_basicBlocks.erase(m_basicBlocks.begin()+BidSortList[i]);
    for(uint i = 0;i < m_basicBlocks.size();i++)
        m_basicBlocks[i]->setId(i);
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        SsaTac* tacHead = m_basicBlocks[i]->getTacHead();
        SsaTac* tacTail = m_basicBlocks[i]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
           if(curTac->type == TAC_IFZ ||
            curTac->type == TAC_IFEQ || curTac->type == TAC_IFNE
            || curTac->type == TAC_IFLT || curTac->type == TAC_IFLE
            || curTac->type == TAC_IFGT || curTac->type == TAC_IFGE)
            {
                char* name = curTac->second->name;
                sprintf(curTac->second->name,"B%d",old2new[atoi(name+1)]);
            }
            else if(curTac->type == TAC_GOTO
                || curTac->type == TAC_LABEL)
            {
                char* name = curTac->first->name;
                sprintf(curTac->first->name,"B%d",old2new[atoi(name+1)]);
            }            
        }while(curTac != tacTail);
        delete tacHeadHead;
    }
   
    BidFlag[blockNum-1] = false;
    for(int i = blockNum-2;i >= 0;i--)
    {
        if(BidFlag[i] == false)
        {
            m_forwardGraph.erase(m_forwardGraph.begin()+i);
            m_backwardGraph.erase(m_backwardGraph.begin()+i);
            continue;
        } 
       
        vector<uint> &succInfo = m_forwardGraph[i];
        for(int j = succInfo.size()-1;j >= 0;j--)
        {
            uint oldBid = succInfo[j];
            if(BidFlag[oldBid] == false)
                succInfo.erase(succInfo.begin()+j);
            else succInfo[j] = old2new[oldBid];
        }
        vector<uint> &prevInfo = m_backwardGraph[i];
        for(int j = prevInfo.size()-1;j >= 0;j--)
        {
            uint oldBid = prevInfo[j];
            if(BidFlag[oldBid] == false)
                prevInfo.erase(prevInfo.begin()+j);
            else prevInfo[j] = old2new[oldBid];
        }
    }
    
    uint exitBlockId = m_basicBlocks.size()-1;
    m_backwardGraph[exitBlockId].clear();
    vector<vector<uint>> printList = getPrintList();
    for(uint i = 0;i < printList.size();i++)
    {
        uint listLen = printList[i].size();
        uint tailNode = printList[i][listLen-1];
        SsaTac* tacTail = m_basicBlocks[tailNode]->getTacTail();
        if(tacTail != NULL && tacTail->type == TAC_GOTO)continue;
        
        m_backwardGraph[exitBlockId].push_back(tailNode);
        m_forwardGraph[tailNode].push_back(exitBlockId);
    }
   
}
void FunctionBlock::deleteBasicBlock(vector<uint> BidList)
{
    deleteBasicBlockPrevWork(BidList);
    if(!m_uName2SsaSymbs.empty() || !m_tName2SsaSymbs.empty())
    cleanVarInfluence(BidList);      
    directDeleteBasicBlock(BidList);  
    vector<uint> startVector;
    vector<uint> endVector;
    vector<uint> deleteBidList;
    startVector.clear();
    endVector.clear();
    for(uint i = 0;i < m_forwardGraph.size();i++)
    {
        for(uint j = 0;j < m_forwardGraph[i].size();j++)
        {
            startVector.push_back(i);
            endVector.push_back(m_forwardGraph[i][j]);
        }
    }
    deleteBidList = s_algorithmExecutor
    ->getUnreachableNodeList(startVector,endVector,0);
    if(deleteBidList.size() != 0)deleteBasicBlock(deleteBidList);
}

void FunctionBlock::cleanVarInfluence(vector<uint> BidList)
{
    for(uint i = 0;i < BidList.size();i++)
    {
        uint needDeleteBid = BidList[i];
        SsaTac* tacHead = m_basicBlocks[needDeleteBid]->getTacHead();
        SsaTac* tacTail = m_basicBlocks[needDeleteBid]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
       
        do
        {
            curTac = curTac->next;
            switch (curTac->type)
            {
            case TAC_INSERT:
                for(uint i = 0;i < curTac->functionSymb.size();i++)
                {
                    if(curTac->functionSymb2Tac[i] == NULL)continue;
                    curTac->functionSymb[i]->useTimes--;
                    deleteUseSsaTac(curTac->functionSymb2Tac[i]);
                }
                break;
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
            case TAC_ARR_L:
                if(curTac->secondPoint != NULL)
                {
                    curTac->second->useTimes--;
                    deleteUseSsaTac(curTac->secondPoint);
                }
                if(curTac->thirdPoint != NULL)
                {
                    curTac->third->useTimes--;
                    deleteUseSsaTac(curTac->thirdPoint);
                }
                break;
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY: 
            case TAC_IFZ:
                if(curTac->secondPoint != NULL)
                {
                    curTac->second->useTimes--;
                    deleteUseSsaTac(curTac->secondPoint);
                }
                break;
            case TAC_ACTUAL:
            case TAC_RETURN:
                if(curTac->firstPoint != NULL)
                {
                    curTac->first->useTimes--;
                    deleteUseSsaTac(curTac->firstPoint);
                }
                break;
            case TAC_ARR_R:
            case TAC_LEA:
                if(curTac->thirdPoint != NULL)
                {
                    curTac->third->useTimes--;
                    deleteUseSsaTac(curTac->thirdPoint);
                }               
                break;
            default:
                break;
            }
            switch (curTac->type)
            {
            case TAC_INSERT:
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
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY: 
            case TAC_ARR_R:
            case TAC_LEA:  
            case TAC_CALL:
                if(curTac->first == NULL)break;
                if(m_uName2SsaSymbs.find(curTac->first->name) != m_uName2SsaSymbs.end()) 
                   m_uName2SsaSymbs.erase(curTac->first->name);
                if(m_tName2SsaSymbs.find(curTac->first->name) != m_tName2SsaSymbs.end()) 
                   m_tName2SsaSymbs.erase(curTac->first->name);                           
                break;
            default:
                break;
            }
        
        } while (curTac != tacTail);
        
    }
}

void FunctionBlock::cleanDirtySsaTac(void)
{
    for(uint i = 0; i <m_basicBlocks.size();i++)
        m_basicBlocks[i]->cleanDirtyTac();
}


void FunctionBlock::getEdgeNeedToSegmentation(
vector<uint>& needSegStartPoints,vector<uint>& needSegEndPoints)
{
    vector<uint> startPoints;
    vector<uint> endPoints;
    needSegStartPoints.clear();
    needSegEndPoints.clear();
    startPoints.clear();
    endPoints.clear();
    for(uint i = 0;i < m_forwardGraph.size();i++)
    {
        for(uint j = 0;j < m_forwardGraph[i].size();j++)
        {
            startPoints.push_back(i);
            endPoints.push_back(m_forwardGraph[i][j]);
        }
    }
    for(uint i = 0;i < startPoints.size();i++)
    {
        uint startPoint = startPoints[i];
        uint endPoint = endPoints[i];    
        if(m_forwardGraph[startPoint].size() > 1 &&
            m_backwardGraph[endPoint].size() > 1)
        {
            needSegStartPoints.push_back(startPoint);
            needSegEndPoints.push_back(endPoint);
        }
    }    
}

void FunctionBlock::addBasicBlockPreWork(void)
{
    uint origExitBlockId = m_basicBlocks.size()-1;
    
    int prevOfEnd = -1;
    for(uint i = 0;i < m_backwardGraph[origExitBlockId].size();i++)
    {
        uint prevBlockId = m_backwardGraph[origExitBlockId][i];
        SsaTac* tacTail = m_basicBlocks[prevBlockId]->getTacTail();
        if(tacTail == NULL)
        {
            prevOfEnd = prevBlockId;
            break;
        }
        if(tacTail->type != TAC_GOTO)
        {
            if(tacTail->type == TAC_RETURN)continue;
            prevOfEnd = prevBlockId;
            break;
        }
    }
    if(prevOfEnd != -1)
    {
        BasicBlock* newBlock = new BasicBlock();
        SsaTac* returnTac = new SsaTac();
        returnTac->type = TAC_RETURN;
        newBlock->setTacHead(returnTac);
        newBlock->setTacTail(returnTac);
        newBlock->setId(origExitBlockId);
        for(uint i = 0;i < m_backwardGraph[origExitBlockId].size();i++)
        {
            uint prevBlockId = m_backwardGraph[origExitBlockId][i];
            if(prevBlockId == prevOfEnd)continue;
            for(uint j = 0;j < m_forwardGraph[prevBlockId].size();i++)
            {
                if(m_forwardGraph[prevBlockId][j] != origExitBlockId)continue;
                m_forwardGraph[prevBlockId][j] = origExitBlockId + 1;
                break;
            }
        }
        
        vector<uint> newVector;
        newVector.clear();
        newVector.push_back(origExitBlockId + 1);
        m_forwardGraph.insert(m_forwardGraph.begin()+m_forwardGraph.size()-1,newVector);
        for(uint i = 0;i < m_backwardGraph[origExitBlockId].size();i++)
        {
            if(m_backwardGraph[origExitBlockId][i] != prevOfEnd)continue;
            m_backwardGraph[origExitBlockId][i] = origExitBlockId;
            break;
        }
        vector<uint> newVectorCopy;
        newVectorCopy.clear();
        newVector.push_back(prevOfEnd);
        m_backwardGraph.insert(m_backwardGraph.begin()+m_backwardGraph.size()-1,newVectorCopy);
        m_basicBlocks[origExitBlockId]->setId(origExitBlockId+1);
        m_basicBlocks.insert(m_basicBlocks.begin()+origExitBlockId,newBlock);
    }

}

void FunctionBlock::edgeSegmentation(void)
{
    vector<uint> needSegStartPoints;
    vector<uint> needSegEndPoints;
    needSegStartPoints.clear();
    needSegEndPoints.clear();
    getEdgeNeedToSegmentation(needSegStartPoints,needSegEndPoints);
    if(needSegStartPoints.size() == 0)return;
    addBasicBlockPreWork();
    uint exitBlockId = m_forwardGraph.size()-1;
    uint addBlockNum = needSegStartPoints.size();
    vector<vector<uint>> newForwardGraph;
    newForwardGraph.clear();
    newForwardGraph.resize(exitBlockId + addBlockNum + 1);

    for(uint i = 0;i < m_forwardGraph.size()-1;i++)
    {
        for(uint j = 0;j < m_forwardGraph[i].size();j++)
        {
            if(m_forwardGraph[i][j] == exitBlockId)
                newForwardGraph[i].push_back(exitBlockId+addBlockNum);
            else newForwardGraph[i].push_back(m_forwardGraph[i][j]);
        }
    }
    
    vector<BasicBlock*> newBlockList(addBlockNum);
    for(uint i = 0;i < needSegStartPoints.size();i++)
    {
        uint startPoint = needSegStartPoints[i];
        uint endPoint = needSegEndPoints[i]; 
        
        
        uint newBlockId = exitBlockId + i;
        uint printSuccOfstartPoint = getBlockPrintSucc(startPoint);
        if(endPoint == exitBlockId || printSuccOfstartPoint == endPoint)
        {
            
            newBlockList[i] = new BasicBlock();
            newBlockList[i]->setId(newBlockId);
            newBlockList[i]->setinstNum(0);
            newBlockList[i]->setTacHead(NULL);
            newBlockList[i]->setTacTail(NULL);
            if(endPoint == exitBlockId)endPoint = exitBlockId + addBlockNum;
            vector<uint>::iterator it = find(newForwardGraph[startPoint].begin(),
                newForwardGraph[startPoint].end(),endPoint);
            if(it == newForwardGraph[startPoint].end()){exit(-1);}
            *it = newBlockId;
            newForwardGraph[newBlockId].push_back(endPoint);
            continue;
        }
        
        uint oldGotoBid;
        SsaTac* tacTail = m_basicBlocks[startPoint]->getTacTail();
        if(tacTail->type == TAC_GOTO)
        {
            oldGotoBid = atoi(tacTail->first->name+1);
            sprintf(tacTail->first->name,"B%d",newBlockId);
        }
        else if(tacTail->type == TAC_IFZ)
        {
            oldGotoBid = atoi(tacTail->second->name+1);
            sprintf(tacTail->second->name,"B%d",newBlockId);
        }
        else exit(-1);
        SsaTac* newLabel = new SsaTac();
        newLabel->type = TAC_LABEL;
        newLabel->first = new SsaSymb();
        newLabel->first->type = SYM_LABEL;
        sprintf(newLabel->first->name,"B%d",newBlockId);

        SsaTac* newGoto = new SsaTac();
        newGoto->type = TAC_GOTO;
        newGoto->first = new SsaSymb();
        newGoto->first->type = SYM_LABEL;
        sprintf(newGoto->first->name,"B%d",oldGotoBid);

        newLabel->next = newGoto;
        newGoto->prev = newLabel;

        newBlockList[i] = new BasicBlock();
        newBlockList[i]->setinstNum(2);
        newBlockList[i]->setTacHead(newLabel);
        newBlockList[i]->setTacTail(newGoto);
        newBlockList[i]->setId(newBlockId);
        vector<uint>::iterator it = find(newForwardGraph[startPoint].begin(),
            newForwardGraph[startPoint].end(),endPoint);
        if(it == newForwardGraph[startPoint].end()){exit(-1);}
        *it = newBlockId;
        newForwardGraph[newBlockId].push_back(endPoint);        
    }
    m_basicBlocks.insert(m_basicBlocks.begin()+m_basicBlocks.size() - 1,
        newBlockList.begin(),newBlockList.end());
    m_forwardGraph.clear();
    m_backwardGraph.clear();
    m_forwardGraph.resize(newForwardGraph.size());
    m_backwardGraph.resize(newForwardGraph.size());
    for(uint i = 0;i < newForwardGraph.size();i++)
    {
        for(uint j = 0; j < newForwardGraph[i].size();j++)
        {
            m_forwardGraph[i].push_back(newForwardGraph[i][j]);
            m_backwardGraph[newForwardGraph[i][j]].push_back(i);
        }
    }
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        m_basicBlocks[i]->setId(i);
    }
}  

uint FunctionBlock::addNewNodeForLoop(uint loopHead,vector<uint> prevBids)
{
    
    addBasicBlockPreWork();
    uint newNodeId = m_basicBlocks.size() - 1;
    BasicBlock* newBlock = new BasicBlock();

    SsaTac* labelTac = new SsaTac();
    labelTac->type = TAC_LABEL;
    SsaSymb* newLabelSymb = new SsaSymb();
    newLabelSymb->type = SYM_LABEL;
    sprintf(newLabelSymb->name,"B%d",newNodeId);
    labelTac->first = newLabelSymb;

    SsaTac* gotoTac = new SsaTac();
    gotoTac->type = TAC_GOTO;
    SsaSymb* newGotoSymb = new SsaSymb();
    newGotoSymb->type = SYM_LABEL;
    sprintf(newGotoSymb->name,"B%d",loopHead);
    gotoTac->first = newGotoSymb;

    labelTac->next = gotoTac;
    gotoTac->prev = labelTac;
    newBlock->setTacHead(labelTac);
    newBlock->setTacTail(gotoTac);
    newBlock->setinstNum(2);
    newBlock->setId(newNodeId);

    for(uint i = 0;i < prevBids.size();i++)
    {
        uint prevBid = prevBids[i];
        SsaTac* tacTail = m_basicBlocks[prevBid]->getTacTail();
        if(tacTail == NULL)continue;
        if(tacTail->type == TAC_GOTO)
            sprintf(tacTail->first->name,"B%d",newNodeId);
        if(tacTail->type == TAC_IFZ)
        {
            uint oldBid = atoi(tacTail->second->name+1);
            if(oldBid != loopHead)continue;
            sprintf(tacTail->second->name,"B%d",newNodeId);
        }
    }
    unordered_set<uint> prevBidSet;
    prevBidSet.clear();
    for(uint i = 0;i < prevBids.size();i++)prevBidSet.insert(prevBids[i]);
    
    do
    {
        if(prevBids.size() != 1)break;
        SsaTac* tacHead = m_basicBlocks[loopHead]->getTacHead();
        SsaTac* tacTail = m_basicBlocks[loopHead]->getTacTail();
        if(tacHead == NULL)break;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        tacHead->prev = tacHeadHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
            if(curTac->type != TAC_INSERT)break;
            vector<SsaSymb*> needMoveVar;  
            vector<uint> needDeletePos;    
            needMoveVar.clear();
            string varName = curTac->first->name;
            int positionOfD = varName.find('d');
            string uVarName = varName.substr(0, positionOfD);
            uint dNumOfNewVar = getMaxDNumOfUVar(varName);
            for(uint i = 0;i < m_backwardGraph[loopHead].size();i++)
            {
                uint prevBid = m_backwardGraph[loopHead][i];
                if(prevBidSet.find(prevBid) == prevBidSet.end())continue;
                needMoveVar.push_back(curTac->functionSymb[i]);
                needDeletePos.push_back(i);
            }
            for(uint i = 0;i < curTac->functionSymb.size();i++)
            {
                if(curTac->functionSymb2Tac[i] == NULL)continue;
                curTac->functionSymb[i]->useTimes--;
                deleteUseSsaTac(curTac->functionSymb2Tac[i]);
            }
            for(int i = needDeletePos.size()-1;i >=0;i--)
            {
                curTac->functionSymb2Tac.erase(
                curTac->functionSymb2Tac.begin()+needDeletePos[i]);
                curTac->functionSymb.erase(
                curTac->functionSymb.begin()+needDeletePos[i]);
            }
           
            SsaTac* insertTac = new SsaTac();
            insertTac->type = TAC_INSERT;
            insertTac->blockId = newNodeId;
            SsaSymb* newSymb = new SsaSymb();
            newSymb->type = SYM_VAR;
            newSymb->defPoint = insertTac;
            sprintf(newSymb->name,"%sd%d",uVarName.c_str(),dNumOfNewVar+1);
            insertTac->first = newSymb;
            insertTac->functionSymb.resize(needMoveVar.size());
            insertTac->functionSymb2Tac.resize(needMoveVar.size());
            for(uint i = 0;i < needMoveVar.size();i++)
            {
                insertTac->functionSymb[i] = needMoveVar[i];
                insertTac->functionSymb2Tac[i] = NULL;
                if(insertTac->functionSymb[i]->type == SYM_INT)continue;
                if(m_tName2SsaSymbs.find(insertTac->functionSymb[i]->name) == m_tName2SsaSymbs.end() &&
                m_uName2SsaSymbs.find(insertTac->functionSymb[i]->name) == m_uName2SsaSymbs.end())continue;
                addTacToUseListForSsaSymb(insertTac,
                insertTac->functionSymb[i],insertTac->functionSymb2Tac[i]);
            }
            newBlock->insertTacToTail(insertTac);
            m_uName2SsaSymbs[newSymb->name] = newSymb;
            curTac->functionSymb.push_back(newSymb);
            curTac->functionSymb2Tac.push_back(NULL);
            for(uint i = 0;i < curTac->functionSymb.size();i++)
            {
                curTac->functionSymb2Tac[i] = NULL;
                if(curTac->functionSymb[i]->type == SYM_INT)continue;
                if(m_tName2SsaSymbs.find(curTac->functionSymb[i]->name) == m_tName2SsaSymbs.end() &&
                m_uName2SsaSymbs.find(curTac->functionSymb[i]->name) == m_uName2SsaSymbs.end())continue;
                addTacToUseListForSsaSymb(curTac,
                curTac->functionSymb[i],curTac->functionSymb2Tac[i]);
            }                
            
        } while (curTac != tacTail);
        delete tacHeadHead;
    } while (0);
   
    for(uint i = 0;i < prevBids.size();i++)
    {
        uint prevBid = prevBids[i];
        vector<uint>::iterator it;
        it = find(m_forwardGraph[prevBid].begin(),m_forwardGraph[prevBid].end(),loopHead);
        if(it == m_forwardGraph[prevBid].end())exit(-1);
        *it = newNodeId;
    }
    m_forwardGraph[newNodeId].clear();
    m_forwardGraph[newNodeId].push_back(loopHead);
    vector<uint> newVector;
    newVector.clear();
    m_forwardGraph.push_back(newVector);
    for(int i = m_backwardGraph[loopHead].size()-1;i>=0;i--)
    {
        uint prevBid = m_backwardGraph[loopHead][i];
        vector<uint>::iterator it = find(m_backwardGraph[loopHead].begin(),
                m_backwardGraph[loopHead].end(),prevBid);
        if(it == m_backwardGraph[loopHead].end())continue;
        m_backwardGraph[loopHead].erase(it);
    }
    m_backwardGraph[loopHead].push_back(newNodeId);
    m_backwardGraph.insert(m_backwardGraph.begin()+m_backwardGraph.size()-1,prevBids);
    
    m_basicBlocks.insert(m_basicBlocks.begin() +
        m_basicBlocks.size() - 1,newBlock);
    m_basicBlocks[m_basicBlocks.size()-1]->setId(m_basicBlocks.size()-1);
    return newNodeId;
}

uint FunctionBlock::getMaxDNumOfUVar(string varName)
{
    uint maxDNum = 0;
    int positionOfD = varName.find('d');
    if(positionOfD == -1)exit(-1);
    string uVarName = varName.substr(0, positionOfD);
    unordered_map<string,SsaSymb*>::iterator it;
    for(it = m_uName2SsaSymbs.begin();it != m_uName2SsaSymbs.end();it++)
    {
        int positionOfDTemp = (it->first).find('d');
        if(positionOfDTemp == -1)continue;
        string uVarNameTemp = varName.substr(0, positionOfDTemp);
        if(uVarName.compare(uVarNameTemp) == -1)continue;
        string dNumString = (it->first).substr(positionOfDTemp+1);
        uint dValue = atoi(dNumString.c_str());
        if(dValue > maxDNum)maxDNum = dValue;
    }
    return maxDNum;
}

void FunctionBlock::deleteExtraGotoBlocks(void)
{
    vector<uint> BidList;
    BidList.clear();
    for(uint i = 0;i < m_basicBlocks.size();i++)
    {
        uint instNum = m_basicBlocks[i]->getInstNum();
        if(instNum != 2)continue;
        SsaTac* tacHead = m_basicBlocks[i]->getTacHead();
        SsaTac* tacTail = m_basicBlocks[i]->getTacTail();
        if(tacHead->type != TAC_LABEL)continue;
        if(tacTail->type != TAC_GOTO)continue;
        if(m_backwardGraph[i].size() != 1)continue;
        if(m_forwardGraph[i].size() != 1)continue;
        uint prevBid = m_backwardGraph[i][0];
        uint succBid = m_forwardGraph[i][0];
        SsaTac* prevTacHead = m_basicBlocks[prevBid]->getTacHead();
        SsaTac* prevTacTail = m_basicBlocks[prevBid]->getTacTail();
        if(prevTacHead == NULL)continue;
        uint continueFlag = true;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = prevTacHead;
        SsaTac* curTac = tacHeadHead;        
        do
        {
            curTac = curTac->next;
            if(curTac->type == TAC_IFZ ||
        curTac->type == TAC_IFEQ || curTac->type == TAC_IFNE
        || curTac->type == TAC_IFLT || curTac->type == TAC_IFLE
        || curTac->type == TAC_IFGT || curTac->type == TAC_IFGE
            )
            {
                uint gotoBId = atoi(curTac->second->name+1);
                if(gotoBId != i)continue;
                sprintf(curTac->second->name,"B%d",succBid);
                continueFlag = false;
            }
            else if(curTac->type == TAC_GOTO)
            {
                uint gotoBId = atoi(curTac->first->name+1);
                if(gotoBId != i)continue;
                sprintf(curTac->first->name,"B%d",succBid);
                continueFlag = false;
            }
        } while (curTac != prevTacTail);
        delete tacHeadHead;
        if(continueFlag)continue;
        vector<uint>::iterator it = find(m_backwardGraph[succBid].begin(),
            m_backwardGraph[succBid].end(),i);
        if(it == m_backwardGraph[succBid].end())exit(-1);
        *it = prevBid;
        it = find(m_forwardGraph[prevBid].begin(),m_forwardGraph[prevBid].end(),i);
        if(it == m_forwardGraph[prevBid].end())exit(-1);
        *it = succBid;
        m_forwardGraph[i].clear();
        m_backwardGraph[i].clear();
        BidList.push_back(i);
    }
    if(BidList.size() == 0)return;
    directDeleteBasicBlock(BidList);
}

#endif
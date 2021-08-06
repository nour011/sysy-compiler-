

#ifndef SSATRANSLATOR_HPP
#define SSATRANSLATOR_HPP
#include <stack>
#include "functionBlock.hpp"
class SsaTranslator
{
private:
    vector<vector<uint>> m_defs;
    vector<vector<uint>> m_DF;
    vector<vector<uint>> m_phiNodesOfVars;
    vector<uint> m_varsCount;               
    vector<vector<uint>> m_mustPassNodeTree;
    vector<stack<uint>> m_varsStack;
    FunctionBlock* m_block;               
private:
    void clear();
    void calcuDefs(void);
    void insertFunctionCode(void);
    void calculPhiNodesOfVars(void);

    void renameVarBaseOnSSA(void);
    void renameEachVar(uint blockId);
    void renameVarInit(void);
    void renameUseVar(SsaSymb* var);
    void renameDefVar(SsaSymb* var,vector<uint>& varList);
    void buildDefUseList(void);
    void replaceSsaSymbInCode(SsaTac* &node,uint num);
public:
    SsaTranslator();
    ~SsaTranslator();
    void printDefs(void);
    void printPhiNodesOfVars(void);
    void printDefUseListForEachVar(void);
    void translateBlockIntoSsa(FunctionBlock* block);
    void eliminateInsertFunction(FunctionBlock* block);
    void solveInsertConflict(FunctionBlock* block);
};
SsaTranslator::SsaTranslator()
{
    clear();
}

void SsaTranslator::clear()
{
    m_DF.clear();
    m_defs.clear();
    m_phiNodesOfVars.clear();
    m_varsCount.clear();
    m_mustPassNodeTree.clear();
    m_varsStack.clear();
    m_block = NULL;
}

SsaTranslator::~SsaTranslator()
{

}

void SsaTranslator::translateBlockIntoSsa(FunctionBlock* block)
{
    m_block = block;
    calcuDefs();
    vector<uint> needToDeleteList;
    vector<uint> numId2varId = m_block->getFuncSymTable()->getNumId2varIdMap();
    needToDeleteList.clear();
    for(uint i = 0;i < m_defs.size();i++)
    {
        if(m_defs[i].size() == 0)
            needToDeleteList.push_back(numId2varId[i]);
    }
    m_block->getFuncSymTable()->deleteVars(needToDeleteList);
    insertFunctionCode();
    renameVarBaseOnSSA();
    buildDefUseList();
    clear();
}



void SsaTranslator::insertFunctionCode(void)
{
    vector<SsaSymb*> numId2symb = m_block->getFuncSymTable()->getNumId2symbMap();
  
    calculPhiNodesOfVars();
  
    vector<vector<uint>>& backwardgraph = m_block->getBackwardGraph();
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    for(uint i = 0;i < m_phiNodesOfVars.size();i++)
    {
        SsaSymb* varSymb = numId2symb[i];
        for(uint j = 0;j < m_phiNodesOfVars[i].size();j++)
        {
            uint blockId = m_phiNodesOfVars[i][j];
            uint size = backwardgraph[blockId].size();
            basicBlocks[blockId]->insertPsiFunction(varSymb,size);
        }
    }
}

void SsaTranslator::calculPhiNodesOfVars(void)
{
    calcuDefs();
    vector<uint> startVector;
    vector<uint> endVector;
    startVector.clear();
    endVector.clear();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    for(uint i = 0;i < forwardGraph.size();i++)
    {
        for(uint j = 0;j < forwardGraph[i].size();j++)
        {
            startVector.push_back(i);
            endVector.push_back(forwardGraph[i][j]);
        }
    }
    m_DF = s_algorithmExecutor->getDominantFrontier(startVector,endVector);
    m_phiNodesOfVars = s_algorithmExecutor->calculPhiNode(m_defs,m_DF);
}

void SsaTranslator::calcuDefs(void)
{
    unordered_map<uint,uint> varId2numId = m_block->m_funcSymTable->getVarId2numIdMap();
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    m_defs.clear();
    m_defs.resize(varId2numId.size());
    for(uint i = 1;i < basicBlocks.size()-1;i++)
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
            switch(curTac->type)
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
                case TAC_NEG:
                case TAC_POSI:
                case TAC_NOT:
                case TAC_COPY:
                case TAC_ARR_R:
                case TAC_ARR_L:
                case TAC_LEA:
                case TAC_FORMAL:
                    {
                        if(curTac->first->type == SYM_VAR &&
                         curTac->first->name[0] == 'u')
                        {
                            int varId = atoi(curTac->first->name+1);
                            int numId = varId2numId[varId];
                            if(m_defs[numId].size()==0)
                                m_defs[numId].push_back(i);
                            else if(m_defs[numId].size()!=0 &&
                                m_defs[numId][m_defs[numId].size()-1] != i)
                                m_defs[numId].push_back(i);
                        }
                    }
                    break;
                case TAC_CALL:
                    {
                        if(curTac->first!=NULL && curTac->first->type == SYM_VAR
                            && curTac->first->name[0] == 'u')
                        {
                            int varId = atoi(curTac->first->name+1);
                            int numId = varId2numId[varId];
                            if(m_defs[numId].size()==0)
                                m_defs[numId].push_back(i);
                            else if(m_defs[numId].size()!=0 &&
                                m_defs[numId][m_defs[numId].size()-1] != i)
                                m_defs[numId].push_back(i);
                        }                        
                    }
                    break;
                default:
                    break;
            }
        }
        while(curTac != tacTail);
        delete tacHeadHead;
    }
}

void SsaTranslator::printDefs(void)
{
    cout << "@" << endl;
    cout << "defs is as follow:" << endl;
    vector<uint> numId2varId = m_block->getFuncSymTable()->getNumId2varIdMap();
    for(uint i = 0;i < m_defs.size();i++)
    {
        cout << "the u" << numId2varId[i] << " is def in the Block:"<< "\t";
        for(uint j = 0;j < m_defs[i].size();j++)
        {
            cout << "B" << m_defs[i][j] << "\t";
        }   
        cout << endl;
    }    
}


void SsaTranslator::printPhiNodesOfVars(void)
{
    cout << "@" << endl;
    cout << "PhiNodesOfVars are as fllow :" << endl;
    vector<uint> numId2varId = m_block->getFuncSymTable()->getNumId2varIdMap();
    for(uint i = 0;i < m_phiNodesOfVars.size();i++)
    {
        cout << "the u" << numId2varId[i] << " need to be inserted in Blocks:"<< "\t";
        for(uint j = 0;j < m_phiNodesOfVars[i].size();j++)
        {
            cout << "B" << m_phiNodesOfVars[i][j] << "\t";
        }   
        cout << endl;
    }     
}



void SsaTranslator::renameVarInit(void)
{
    uint varNum = m_block->getFuncSymTable()
        ->getNumId2varIdMap().size();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    
    m_varsCount.resize(varNum);                            
    for(uint i = 0;i < varNum;i++)m_varsCount[i] = 0;
 
    vector<uint> startVector;
    vector<uint> endVector;
    startVector.clear();
    endVector.clear();
    for(uint i = 0;i < forwardGraph.size();i++)
    {
        for(uint j = 0;j < forwardGraph[i].size();j++)
        {
            startVector.push_back(i);
            endVector.push_back(forwardGraph[i][j]);
        }
    }
    vector<uint> dominantTreeIdom = 
        s_algorithmExecutor->getDominantTreeIdom(startVector,endVector);
    m_mustPassNodeTree.clear();
    m_mustPassNodeTree.resize(dominantTreeIdom.size()/2);
    for(uint i = 0;i < m_mustPassNodeTree.size();i++)m_mustPassNodeTree[i].clear();
    for(uint i = 0;i < m_mustPassNodeTree.size();i++)
    {
        uint idomNode = dominantTreeIdom[i*2+1];
        uint sonNode = dominantTreeIdom[i*2];
        if(idomNode==sonNode)continue;
        m_mustPassNodeTree[idomNode].push_back(sonNode);
    }
    m_varsStack.clear();
    m_varsStack.resize(varNum);
    for(uint i = 0;i < varNum;i++)
    {
        while(!m_varsStack[i].empty())
            m_varsStack[i].pop();
        m_varsStack[i].push(0);
    }
}

void SsaTranslator::renameVarBaseOnSSA(void)
{
    renameVarInit();
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    renameEachVar(0);
}

void SsaTranslator::renameDefVar(SsaSymb* var,vector<uint>& varList)
{
    if(var->type == SYM_VAR && var->name[0] == 'u')
    {
        unordered_map<uint,uint> varId2numId = 
            m_block->getFuncSymTable()->getVarId2numIdbMap();
        uint varId = atoi(var->name+1);
        uint numId = varId2numId[varId];
        m_varsCount[numId]++;
        m_varsStack[numId].push(m_varsCount[numId]);
        sprintf(var->name,"u%dd%d",varId,m_varsCount[numId]);
        varList.push_back(varId);
    }
}
void SsaTranslator::renameUseVar(SsaSymb* var)
{
    if(var->type == SYM_VAR && var->name[0] == 'u')
    {
        unordered_map<uint,uint> varId2numId = 
            m_block->getFuncSymTable()->getVarId2numIdbMap();
        uint varId = atoi(var->name+1);
        uint numId = varId2numId[varId];
        uint nameId = m_varsStack[numId].top();
        sprintf(var->name,"u%dd%d",varId,nameId);
    }
}

void SsaTranslator::renameEachVar(uint blockId)
{
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    SsaTac* sTacHead = basicBlocks[blockId]->getTacHead();
    SsaTac* sTacTail = basicBlocks[blockId]->getTacTail();
    unordered_map<uint,uint> varId2numId = 
        m_block->getFuncSymTable()->getVarId2numIdbMap();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    vector<uint> varList;
    varList.clear();
    SsaTac* tacHeadHead = new SsaTac();
    tacHeadHead->next = sTacHead;
    SsaTac* curTac = tacHeadHead;
    do
    {
        curTac = curTac->next;
        if(curTac == NULL)break;
        switch(curTac->type)
        {
        case TAC_INSERT:
            renameDefVar(curTac->first,varList);
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
            renameDefVar(curTac->first,varList);
            renameUseVar(curTac->second);
            renameUseVar(curTac->third);
            break;
        case TAC_ARR_L:
            renameUseVar(curTac->second);
            renameUseVar(curTac->third);
            break;
        case TAC_ARR_R:
        case TAC_LEA:
            renameDefVar(curTac->first,varList);
            renameUseVar(curTac->third);
            break;
        case TAC_NEG:
        case TAC_NOT:
        case TAC_POSI:
        case TAC_COPY:
            renameDefVar(curTac->first,varList);
            renameUseVar(curTac->second);
            break;
        case TAC_IFZ:
        case TAC_ACTUAL:
            renameUseVar(curTac->first);
            break;
        case TAC_RETURN:
            if(curTac->first != NULL)
                renameUseVar(curTac->first);
            break;
        case TAC_FORMAL:
            renameDefVar(curTac->first,varList);
            break;
        case TAC_CALL:
            renameDefVar(curTac->first,varList);
            break;
        default:
            break;            
        }
    } while (curTac != sTacTail);
    delete tacHeadHead;
    for(uint i = 0;i < forwardGraph[blockId].size();i++)
        uint sonBlockId = forwardGraph[blockId][i];
        uint fatherOrder = 0;
        while(backwardGraph[sonBlockId][fatherOrder] != blockId)fatherOrder++;
        SsaTac* tacHead = basicBlocks[sonBlockId]->getTacHead();
        SsaTac* tacTail = basicBlocks[sonBlockId]->getTacTail();
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
            if(curTac == NULL || curTac->type != TAC_INSERT)break;
            renameUseVar(curTac->functionSymb[fatherOrder]);
        } while (curTac != tacTail);
        delete tacHeadHead;
    }
    for(uint i = 0;i < m_mustPassNodeTree[blockId].size();i++)
    {
        renameEachVar(m_mustPassNodeTree[blockId][i]);
    }
    for(uint i = 0;i<varList.size();i++)
    {
        uint varId = varList[i];
        uint numId = varId2numId[varId];
        m_varsStack[numId].pop();
    }
}



void SsaTranslator::buildDefUseList(void)
{

    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    uName2SsaSymbs.clear();
    tName2SsaSymbs.clear();
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
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY:
            case TAC_ARR_R:
            case TAC_FORMAL:
            case TAC_LEA:
            case TAC_CALL:
            case TAC_INSERT:
                if(curTac->first->type == SYM_VAR &&
                    curTac->first->name[0] == 'u')
                {
                    uName2SsaSymbs[curTac->first->name]
                            = curTac->first;
                    setDefPointForSsaSymb(curTac,curTac->first);
                }
                else if(curTac->first->name[0] == 't')
                {
                    tName2SsaSymbs[curTac->first->name] 
                        = curTac->first;
                    setDefPointForSsaSymb(curTac,curTac->first);
                }

                break;
            }
        } while (curTac != tacTail);
        delete tacHeadHead;
    }
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
            switch (curTac->type)
            {
            case TAC_INSERT:
                for(uint j = 0;j < curTac->functionSymb.size();j++)
                {
                    SsaSymb* varSymb = curTac->functionSymb[j];
                    unordered_map<string,SsaSymb*>::iterator it =
                        uName2SsaSymbs.find(varSymb->name);
                    if(it == uName2SsaSymbs.end())continue;
                    SsaSymb* mapSymb = it->second;
                    curTac->functionSymb[j] = mapSymb;
                    addTacToUseListForSsaSymb(curTac,mapSymb,curTac->functionSymb2Tac[j]);
                    delete varSymb;
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
                replaceSsaSymbInCode(curTac,2);
                replaceSsaSymbInCode(curTac,3);
                break;
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY:
                replaceSsaSymbInCode(curTac,2);
                break;
                break;
            case TAC_IFZ:
            case TAC_ACTUAL:
                replaceSsaSymbInCode(curTac,1);
                break;
            case TAC_LEA:
                replaceSsaSymbInCode(curTac,3);
                    break;
            case TAC_ARR_R:
                replaceSsaSymbInCode(curTac,1);
                replaceSsaSymbInCode(curTac,3);
                break;
            case TAC_RETURN:
                if(curTac->first != NULL)
                    replaceSsaSymbInCode(curTac,1);
                break;
            }
        } while (curTac != tacTail);
        delete tacHeadHead;
    }
}

void SsaTranslator::replaceSsaSymbInCode(SsaTac* &node,uint num)
{
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    switch(num)
    {
    case 1:
        {
            SsaSymb* firstVarSymb = node->first;
            unordered_map<string,SsaSymb*>::iterator it;
            if(firstVarSymb->type == SYM_VAR &&
                firstVarSymb->name[0] == 'u')
            {
                it = uName2SsaSymbs.find(firstVarSymb->name);
                if(it == uName2SsaSymbs.end())return;
            }
            else if(firstVarSymb->name[0] == 't')
            {
                it = tName2SsaSymbs.find(firstVarSymb->name);
                if(it == tName2SsaSymbs.end())return;
            }
            else return;
            SsaSymb* firstMapSymb = it->second;
            node->first = firstMapSymb;
            addTacToUseListForSsaSymb(node,firstMapSymb,node->firstPoint);
        }
        return;
    case 2:
        {
            SsaSymb* secondVarSymb = node->second;
            unordered_map<string,SsaSymb*>::iterator it;
            if(secondVarSymb->type == SYM_VAR &&
                secondVarSymb->name[0] == 'u')
            {
                it = uName2SsaSymbs.find(secondVarSymb->name);
                if(it == uName2SsaSymbs.end())return;
            }
            else if(secondVarSymb->name[0] == 't')
            {
                it = tName2SsaSymbs.find(secondVarSymb->name);
                if(it == tName2SsaSymbs.end())return;
            }
            else return;
            SsaSymb* secondMapSymb = it->second;
            node->second = secondMapSymb;
            addTacToUseListForSsaSymb(node,secondMapSymb,node->secondPoint);
        }
        return;    
    case 3:
        {
            SsaSymb* thirdVarSymb = node->third;
            unordered_map<string,SsaSymb*>::iterator it;
            if(thirdVarSymb->type == SYM_VAR &&
                thirdVarSymb->name[0] == 'u')
            {
                it = uName2SsaSymbs.find(thirdVarSymb->name);
                if(it == uName2SsaSymbs.end())return;
            }
            else if(thirdVarSymb->name[0] == 't')
            {
                it = tName2SsaSymbs.find(thirdVarSymb->name);
                if(it == tName2SsaSymbs.end())return;
            }
            else return;
            SsaSymb* thirdMapSymb = it->second;
            node->third = thirdMapSymb;
            addTacToUseListForSsaSymb(node,thirdMapSymb,node->thirdPoint);
        }
        return;   
    }
}

void SsaTranslator::printDefUseListForEachVar(void)
{
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    cout << endl << "the def-use List for each u var are as followed:" << endl;
    unordered_map<string,SsaSymb*>::iterator it = uName2SsaSymbs.begin();
    for(;it != uName2SsaSymbs.end();it++)
    {
        cout << "var: " << it->first << "\tnum:" << it->second->useTimes <<  endl;
        SsaSymb* varSymb = it->second;
        for(UseSsaTac* curTac = varSymb->useList;
        curTac->next != NULL;curTac = curTac->next)
        {
            printOneSsaTac(curTac->next->code);
            cout << endl;
        }
    }
    cout << endl << "the def-use List for each t var are as followed:" << endl;
    it = tName2SsaSymbs.begin();
    for(;it != tName2SsaSymbs.end();it++)
    {
        cout << "var: " << it->first << "\tnum:" << it->second->useTimes <<  endl;
        SsaSymb* varSymb = it->second;
        for(UseSsaTac* curTac = varSymb->useList;
        curTac->next != NULL;curTac = curTac->next)
        {
            printOneSsaTac(curTac->next->code);
            cout << endl;
        }        
    }
}

void SsaTranslator::eliminateInsertFunction(FunctionBlock* block)
{   
    clear();
    m_block = block;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    for(uint blockId = 0;blockId < basicBlocks.size();blockId++)
    {
        SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
        SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;        
        do
        {
            curTac = curTac->next;
            if(curTac->type != TAC_INSERT)break;
            for(uint i = 0;i < backwardGraph[blockId].size();i++)
            {
                uint prevBlockId = backwardGraph[blockId][i];
                
                SsaSymb* functionSymb = curTac->functionSymb[i];
                if(functionSymb == curTac->first)continue;
                if(functionSymb->type == SYM_VAR && 
                    functionSymb->name[0] =='u')
                {
                    unordered_map<string,SsaSymb*>::iterator it;
                    it = uName2SsaSymbs.find(functionSymb->name);
                    if(it == uName2SsaSymbs.end())continue;
                }
                SsaTac* newTac = new SsaTac();
                newTac->type = TAC_COPY;
                newTac->first = curTac->first;
                newTac->second = functionSymb;
                basicBlocks[prevBlockId]->insertTacToTail(newTac);
            }
            curTac->type = TAC_UNDEF;
        } while (curTac != tacTail);
        delete tacHeadHead;
        basicBlocks[blockId]->cleanDirtyTac();
    } 
}

void SsaTranslator::solveInsertConflict(FunctionBlock* block)
{
    clear();
    m_block = block;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    for(uint blockId = 0;blockId < basicBlocks.size();blockId++)
    {
        SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
        SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
        vector<SsaTac*> insertTacVector;
        vector<SsaTac*> reArrangeTacVector;
        insertTacVector.clear();
        reArrangeTacVector.clear();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {   
            curTac = curTac->next;
            if(curTac->type != TAC_INSERT)break;
            curTac->type = TAC_UNDEF;
            insertTacVector.push_back(curTac);
        }while(curTac != tacTail);
        if(insertTacVector.size() == 0)continue;
        basicBlocks[blockId]->raiseUnUseTac();
        unordered_set<SsaSymb*> symbList;
        reArrangeTacVector.push_back(insertTacVector[0]);
        for(uint i = 1;i < insertTacVector.size();i++)
        {
            symbList.clear();
            SsaTac* insertTac = insertTacVector[i];
            for(uint j = 0;j < insertTac->functionSymb.size();j++)
                symbList.insert(insertTac->functionSymb[j]);
            uint placeId = reArrangeTacVector.size();
            for(int j = reArrangeTacVector.size()-1;j >= 0;j--)
            {
                unordered_set<SsaSymb*>::iterator it;
                it = symbList.find(reArrangeTacVector[j]->first);
                if(it == symbList.end())continue;
                placeId = j;
            }
            reArrangeTacVector.insert(reArrangeTacVector.begin() + 
                placeId,insertTac);
        }
        for(uint i = 0;i < reArrangeTacVector.size();i++)
        {
            reArrangeTacVector[i]->type = TAC_INSERT;
            basicBlocks[blockId]->insertTacToTail(reArrangeTacVector[i]);
        }
    }
}
#endif


#ifndef BASICBLOCKEXECUTOR_HPP
#define BASICBLOCKEXECUTOR_HPP
#include "globalPolicyExecutor.hpp"

class ArrayAssignUnit
{
public:
    unordered_map<string,SsaSymb*> m_index2Ssa;
public:
    void clear(){m_index2Ssa.clear();}
    void add(string index,SsaSymb* varSymb)
    {
        m_index2Ssa[index] = varSymb;
    }
    void add(uint index,SsaSymb* varSymb)
    {
        string indexString = to_string(index);
        m_index2Ssa[indexString] = varSymb;
    }
    SsaSymb* find(uint index)
    {
        unordered_map<string,SsaSymb*>::iterator it;
        string indexString = to_string(index);
        it = m_index2Ssa.find(indexString);
        if(it != m_index2Ssa.end())return it->second;
        return NULL;
    }
    SsaSymb* find(string index)
    {
        unordered_map<string,SsaSymb*>::iterator it;
        it = m_index2Ssa.find(index);
        if(it != m_index2Ssa.end())return it->second;
        return NULL;
    }
    bool isHaveUnkownIndex(void)
    {
        for(auto it = m_index2Ssa.begin();it!=m_index2Ssa.end();it++)
        {
            string indexName = it->first;
            const char* name = indexName.c_str();
            for(uint i = 0;i < indexName.size();i++)
            {
                if(name[i] < '0')return true;
                if(name[i] > '9')return true;
            }
        }
        return false;
    }
    ArrayAssignUnit(){clear();};
    ~ArrayAssignUnit(){};
};

class GlobalVarAssignUnit
{
public:
    unordered_map<string,SsaSymb*> m_index2Ssa;
public:
    void clear(){m_index2Ssa.clear();}
    void add(string index,SsaSymb* varSymb)
    {
        m_index2Ssa[index] = varSymb;
    }
    SsaSymb* find(string index)
    {
        unordered_map<string,SsaSymb*>::iterator it;
        it = m_index2Ssa.find(index);
        if(it != m_index2Ssa.end())return it->second;
        return NULL;
    }
    GlobalVarAssignUnit(){clear();};
    ~GlobalVarAssignUnit(){};
};


class BasicBlockExecutor:
public GlobalPolicyExecutor
{
private:
    bool m_isOptimize;
    FunctionBlock* m_block;
    FuncPropertyGetter* m_funcPropertyGetter;
    unordered_map<string,ArrayAssignUnit*> m_arrAssignUnit;
    GlobalVarAssignUnit* m_glbalVarAssignUnit;
    vector<bool> m_isBlockSearch;
private:
    void clear();
    SsaSymb* lookForValue(SsaSymb* varSymb);
    void actionOfCopy(SsaTac* tacNode);
    void actionOfTwoOperands(SsaTac* tacNode);
    void actionOfOneOperand(SsaTac* tacNode);
    void actionOfArrAssign(SsaTac* &tacNode);
    void actionOfArrSpread(SsaTac* &tacNode);
  
    void actionOfGlobalVarAssign(SsaTac* &tacNode);
    void actionOfGlobalVarSpread(SsaTac* &tacNode);

    bool isSymbAConstant(SsaSymb* testSymb,SsaSymb* &varSymb);
    
public:
    BasicBlockExecutor();
    ~BasicBlockExecutor();
    void printInfoOfOptimizer(void);
    void dealWithABlock(uint block);
    bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter);
};

BasicBlockExecutor::BasicBlockExecutor()
{
    m_glbalVarAssignUnit = new GlobalVarAssignUnit();
    m_name = "全局变量与数组优化器";
    clear();
}

BasicBlockExecutor::~BasicBlockExecutor()
{
}
void BasicBlockExecutor::clear()
{
    m_block = NULL;
    m_funcPropertyGetter = NULL;
    m_isOptimize = false;
    m_glbalVarAssignUnit->clear();
    m_arrAssignUnit.clear();
    m_isBlockSearch.clear();
}
void BasicBlockExecutor::printInfoOfOptimizer(void)
{
    
}
bool BasicBlockExecutor::runOptimizer(FunctionBlock* block,
    FuncPropertyGetter* funcPropertyGetter)
{
    clear();
    m_block = block;
    m_funcPropertyGetter = funcPropertyGetter;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    m_isBlockSearch.resize(basicBlocks.size());
    for(uint i = 0;i < m_isBlockSearch.size();i++)m_isBlockSearch[i] = false;
    for(uint i = 0;i < basicBlocks.size();i++)
    {
        if(m_isBlockSearch[i] == true)continue;
        dealWithABlock(i);
        m_arrAssignUnit.clear();
        m_glbalVarAssignUnit->clear();
    }
        
    return m_isOptimize;
}

void BasicBlockExecutor::dealWithABlock(uint block)
{

    BasicBlock* &basicBlock = m_block->getBasicBlocks()[block];
    SsaTac* tacHead = basicBlock->getTacHead();
    SsaTac* tacTail = basicBlock->getTacTail();
    unordered_set<string> dirtyArrName = m_funcPropertyGetter->getDirtyArrName();
    if(tacHead != NULL)
    {
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        tacHead->prev = tacHeadHead;
        SsaTac* curTac = tacHeadHead;
        
        do
        {
            curTac = curTac->next;
            switch (curTac->type)
            {
            
            case TAC_COPY:
                actionOfGlobalVarAssign(curTac);
                actionOfGlobalVarSpread(curTac);
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
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_IFZ:
            case TAC_ACTUAL:
                actionOfGlobalVarSpread(curTac);
                break;    
            case TAC_ARR_L:
               
                actionOfArrAssign(curTac);
                actionOfGlobalVarSpread(curTac);
                break;
            case TAC_ARR_R:
               
                if(curTac->second->name[0] == 'g' && 
                dirtyArrName.find(curTac->second->name) == dirtyArrName.end()
                && curTac->third->type == SYM_INT)
                {
                    curTac->type = TAC_COPY;
                    SsaSymb* varSymb = new SsaSymb();
                    varSymb->type = SYM_INT;
                    varSymb->value = m_block->s_globalSymTable->getValueOfArr(
                        curTac->second->name,curTac->third->value);
                    curTac->second = varSymb;
                    curTac->third = NULL;
                    m_isOptimize = true;
                    break;
                }
                
                actionOfArrSpread(curTac);
                actionOfGlobalVarSpread(curTac);
                break;
            default:
                break;
            }
        } while (curTac != tacTail);
    }

    m_isBlockSearch[block] = true;
  
    vector<vector<uint>> forwardGraph = m_block->getForwardGraph();
    vector<vector<uint>> backwardGraph = m_block->getBackwardGraph();
    if(forwardGraph[block].size() != 1)return;
    uint nextBlockId = forwardGraph[block][0];
    if(m_isBlockSearch[nextBlockId] == true)return;
    if(backwardGraph[nextBlockId].size() != 1)return;
    BasicBlock* &nextBlock = m_block->getBasicBlocks()[nextBlockId];
    SsaTac* nextTacHead = nextBlock->getTacHead();
    SsaTac* nextTacTail = nextBlock->getTacTail(); 
    bool isContinue = true;   
    if(nextTacHead != NULL)
    {
        SsaTac* nextTacHeadHead = new SsaTac();
        nextTacHeadHead->next = nextTacHead;
        SsaTac* nextCurTac = nextTacHeadHead;
        do
        {
            nextCurTac = nextCurTac->next;
            if(nextCurTac->type == TAC_CALL)
            {
                if(m_funcPropertyGetter->isFuncASimpleExpression
                    (nextCurTac->second->name) == false)
                {
                    isContinue = false;
                    break;
                }
            }
        }while(nextCurTac != nextTacTail);
        delete nextTacHeadHead;
    }
    if(isContinue)dealWithABlock(nextBlockId);

}

void BasicBlockExecutor::actionOfArrAssign(SsaTac* &tacNode)
{
   
    ArrayAssignUnit* curArr;
    unordered_map<string,ArrayAssignUnit*>::iterator it;
    it = m_arrAssignUnit.find(tacNode->first->name);
    if(it == m_arrAssignUnit.end())
    {
        curArr = new ArrayAssignUnit();
        m_arrAssignUnit[tacNode->first->name] = curArr;
    }
    else curArr = it->second;
    if(tacNode->second->type != SYM_INT)
    {
        curArr->clear();
        if(tacNode->second->name[0] == 'g')return;
        string indexName = tacNode->second->name;
        SsaSymb* varSymb = tacNode->third;
        curArr->add(indexName,varSymb);
        return;
    }
    
    if(tacNode->third->type == SYM_VAR && 
        tacNode->third->name[0] == 'g')return;
    
    uint index = tacNode->second->value;
    SsaSymb* varSymb = tacNode->third;  
    
    if(curArr->isHaveUnkownIndex())
        curArr->clear();
    curArr->add(index,varSymb);
}


void BasicBlockExecutor::actionOfArrSpread(SsaTac* &tacNode)
{
  
    ArrayAssignUnit* curArr;
    unordered_map<string,ArrayAssignUnit*>::iterator it;
    it = m_arrAssignUnit.find(tacNode->second->name);
    if(it == m_arrAssignUnit.end())
    {
        curArr = new ArrayAssignUnit();
        m_arrAssignUnit[tacNode->second->name] = curArr;
    }
    else curArr = it->second;
    string index;
    if(tacNode->third->type != SYM_INT && 
        tacNode->third->name[0] == 'g')return;
    if(tacNode->third->type != SYM_INT)
        index = tacNode->third->name;
    else index = to_string(tacNode->third->value);
    SsaSymb* varSymb = curArr->find(index);
    
    if(varSymb == NULL)
    {
        if(tacNode->first->name[0] != 'g')
            curArr->add(index,tacNode->first);
        return;
    }

    if(tacNode->third->type != SYM_INT)
    {
        tacNode->third->useTimes--;
        deleteUseSsaTac(tacNode->thirdPoint);
        tacNode->thirdPoint = NULL;
    }
    m_isOptimize = true;
    if(varSymb->type == SYM_INT)
    {
        tacNode->type = TAC_COPY;
        SsaSymb* secondVar = new SsaSymb();
        secondVar->type = SYM_INT;
        secondVar->value = varSymb->value;
        tacNode->second = secondVar;
    }
    else 
    {
        tacNode->type = TAC_COPY;
        tacNode->second = varSymb;
        addTacToUseListForSsaSymb(tacNode,
            tacNode->second,tacNode->secondPoint);
    }
}



void BasicBlockExecutor::actionOfGlobalVarAssign(SsaTac* &tacNode)
{
    if(tacNode->first->name[0] != 'g')return;
    m_glbalVarAssignUnit->add(tacNode->first->name,tacNode->second);
}

void BasicBlockExecutor::actionOfGlobalVarSpread(SsaTac* &tacNode)
{
    SsaSymb* firstSymb = NULL;
    SsaSymb* secondSymb = NULL;
    SsaSymb* thirdSymb = NULL;
    switch (tacNode->type)
    {
        case TAC_COPY:
        case TAC_NEG:
        case TAC_POSI:
        case TAC_NOT:
            if(tacNode->second->type == SYM_INT)break;
            if(tacNode->second->name[0] != 'g')break;
            secondSymb = m_glbalVarAssignUnit->find(tacNode->second->name);
            if(secondSymb == NULL)return;
            tacNode->second = secondSymb;
            if(secondSymb->name[0] == 'g')return;
        addTacToUseListForSsaSymb(tacNode,
            tacNode->second,tacNode->secondPoint);
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
            do
            {
                if(tacNode->second->type == SYM_INT)break;
                if(tacNode->second->name[0] != 'g')break;
                secondSymb = m_glbalVarAssignUnit->find(tacNode->second->name);
                if(secondSymb == NULL)break;
                tacNode->second = secondSymb;
                if(secondSymb->name[0] == 'g')break;
            addTacToUseListForSsaSymb(tacNode,
                tacNode->second,tacNode->secondPoint);                
            } while (0);

            do
            {
                if(tacNode->third->type == SYM_INT)break;
                if(tacNode->third->name[0] != 'g')break;
                thirdSymb = m_glbalVarAssignUnit->find(tacNode->third->name);
                if(thirdSymb == NULL)break;
                tacNode->third = thirdSymb;
                if(thirdSymb->name[0] == 'g')break;
            addTacToUseListForSsaSymb(tacNode,
                tacNode->third,tacNode->thirdPoint);                
            } while (0);            

            break;
        
        
        case TAC_IFZ:
        case TAC_ACTUAL:
            do
            {
                if(tacNode->first->type == SYM_INT)break;
                if(tacNode->first->name[0] != 'g')break;
                firstSymb = m_glbalVarAssignUnit->find(tacNode->first->name);
                if(firstSymb == NULL)break;
                tacNode->first = firstSymb;
                if(firstSymb->name[0] == 'g')break;
            addTacToUseListForSsaSymb(tacNode,
                tacNode->first,tacNode->firstPoint);                
            } while (0);
            break; 
        case TAC_ARR_R:
            do
            {
                if(tacNode->third->type == SYM_INT)break;
                if(tacNode->third->name[0] != 'g')break;
                thirdSymb = m_glbalVarAssignUnit->find(tacNode->third->name);
                if(thirdSymb == NULL)break;
                tacNode->third = thirdSymb;
                if(thirdSymb->name[0] == 'g')break;
            addTacToUseListForSsaSymb(tacNode,
                tacNode->third,tacNode->thirdPoint);                
            } while (0);
            break;
    
    default:
        break;
    }
}
#endif
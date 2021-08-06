#ifndef DELGLOBALEXPROR_HPP
#define DELGLOBALEXPROR_HPP
#include "globalPolicyExecutor.hpp"
#include <string>
using namespace std;

class DelGlobalExpror:
public GlobalPolicyExecutor
{
private:
    bool m_isOptimize;
    unordered_map<uint,string> m_tacTypeToString;
    unordered_map<string,string> m_expressTable;
    vector<vector<uint>> m_mustPassNodeTree;
    FuncPropertyGetter* m_funcPropertyGetter;
private:
    void clear();
    bool weakeningTac(SsaTac* curTac);
    bool checkTheSymbVar(SsaSymb* varSymb);
    void deleteCommonExpression(uint blockId);
    string getStringOfSymb(SsaSymb* varSymb);
    void addExpressionIntoTable(SsaTac* curTac,vector<string>& needDeleteList);
public:
    DelGlobalExpror();
    ~DelGlobalExpror();
    void printInfoOfOptimizer(void);
    bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter);
};

DelGlobalExpror::DelGlobalExpror()
{
    m_name = "表达式删除器";
    clear();
}

void DelGlobalExpror::clear()
{
    m_block = NULL;
    m_isOptimize = false;
    m_expressTable.clear();
    m_tacTypeToString.clear();
    m_tacTypeToString[TAC_ADD] = "+";
    m_tacTypeToString[TAC_SUB] = "-";
    m_tacTypeToString[TAC_MUL] = "*";
    m_tacTypeToString[TAC_DIV] = "/";
    m_tacTypeToString[TAC_EQ] = "==";
    m_tacTypeToString[TAC_MOD] = "%%";
    m_tacTypeToString[TAC_NE] = "!=";
    m_tacTypeToString[TAC_LT] = "<";
    m_tacTypeToString[TAC_LE] = "<=";
    m_tacTypeToString[TAC_GT] = ">";
    m_tacTypeToString[TAC_GE] = ">=";
    m_tacTypeToString[TAC_OR] = "||";
    m_tacTypeToString[TAC_AND] = "&&";
    m_tacTypeToString[TAC_NEG] = "-";
    m_tacTypeToString[TAC_NOT] = "!";
    m_tacTypeToString[TAC_LEA] = "&[]";
    m_tacTypeToString[TAC_CALL] = "call";
}

DelGlobalExpror::~DelGlobalExpror()
{
}

void DelGlobalExpror::printInfoOfOptimizer(void)
{

}

bool DelGlobalExpror::runOptimizer(FunctionBlock* block,
    FuncPropertyGetter* funcPropertyGetter)
{
    clear();
    m_block = block;
    m_funcPropertyGetter = funcPropertyGetter;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
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
    vector<uint> dominantTreeIdom = s_algorithmExecutor->
        getDominantTreeIdom(startVector,endVector);
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
    deleteCommonExpression(0);
    return m_isOptimize;
}

void DelGlobalExpror::deleteCommonExpression(uint blockId)
{
    vector<string> needToDelete;
    needToDelete.clear();
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();    
    vector<vector<uint>> backwardGraph = m_block->getBackwardGraph();
    
    SsaTac* tacHead = basicBlocks[blockId]->getTacHead();
    SsaTac* tacTail = basicBlocks[blockId]->getTacTail();
    if(tacHead != NULL)
    {
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            string secondOperands,thirdOperands;
            string needSymbol,expression;
            unordered_map<string,string>::iterator it;
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
                if(weakeningTac(curTac))break;
                if(!checkTheSymbVar(curTac->second))break;
                if(!checkTheSymbVar(curTac->third))break;       
                
                secondOperands = getStringOfSymb(curTac->second);
                thirdOperands = getStringOfSymb(curTac->third);
                needSymbol = m_tacTypeToString[curTac->type];
                expression = secondOperands + " " + needSymbol + " " + thirdOperands;
                it = m_expressTable.find(expression);
                if(it == m_expressTable.end())
                {
                    if(!checkTheSymbVar(curTac->first))break;
                    addExpressionIntoTable(curTac,needToDelete);
                }
                else
                {
                    string needToReplace = m_expressTable[expression];
                    SsaSymb* copySymb;
                    if(needToReplace.c_str()[0] == 't')
                        copySymb = tName2SsaSymbs[needToReplace];
                    else copySymb = uName2SsaSymbs[needToReplace];
                    curTac->second->useTimes--;
                    curTac->third->useTimes--;
                    deleteUseSsaTac(curTac->secondPoint);
                    deleteUseSsaTac(curTac->thirdPoint);
                    curTac->second = copySymb;
                    curTac->third = NULL;
                    addTacToUseListForSsaSymb(curTac,copySymb,curTac->secondPoint);
                    curTac->thirdPoint = NULL;
                    curTac->type = TAC_COPY;
                    m_isOptimize = true;
                }
                
                break;
            case TAC_NEG:
            case TAC_NOT:
                if(!checkTheSymbVar(curTac->second))break;
                secondOperands = getStringOfSymb(curTac->second);
                needSymbol = m_tacTypeToString[curTac->type];
                expression = needSymbol + " " + secondOperands;
                it = m_expressTable.find(expression);
                if(it == m_expressTable.end())
                {
                    if(!checkTheSymbVar(curTac->first))break;
                    addExpressionIntoTable(curTac,needToDelete);
                }
                else//说明有，则可以用来替换该变量
                {
                    string needToReplace = m_expressTable[expression];
                    SsaSymb* copySymb;
                    if(needToReplace.c_str()[0] == 't')
                        copySymb = tName2SsaSymbs[needToReplace];
                    else copySymb = uName2SsaSymbs[needToReplace];
                    curTac->second->useTimes--;
                    deleteUseSsaTac(curTac->secondPoint);
                    curTac->second = copySymb;
                    addTacToUseListForSsaSymb(curTac,copySymb,curTac->secondPoint);
                    curTac->type = TAC_COPY;
                    m_isOptimize = true;
                }
                break;
            case TAC_LEA:
                
                if(curTac->third->type != SYM_INT &&
                curTac->third->name[0] == 'g')break;
                secondOperands = getStringOfSymb(curTac->second);
                thirdOperands =  getStringOfSymb(curTac->third);
                needSymbol = m_tacTypeToString[curTac->type];
                expression = secondOperands + " " + needSymbol + " " + thirdOperands;
                it = m_expressTable.find(expression);
                if(it == m_expressTable.end())
                {
                    if(curTac->first->name[0] == 'g')break;
                    addExpressionIntoTable(curTac,needToDelete);
                }
                else
                {
                    string needToReplace = m_expressTable[expression];
                    SsaSymb* copySymb;
                    if(needToReplace.c_str()[0] == 't')
                        copySymb = tName2SsaSymbs[needToReplace];
                    else copySymb = uName2SsaSymbs[needToReplace];
                    curTac->third->useTimes--;
                    deleteUseSsaTac(curTac->thirdPoint);
                    curTac->second = copySymb;
                    curTac->third = NULL;
                    addTacToUseListForSsaSymb(curTac,copySymb,curTac->secondPoint);
                    curTac->thirdPoint = NULL;
                    curTac->type = TAC_COPY;
                    m_isOptimize = true;
                }
                break;
            case TAC_CALL:
                {
                    
                    if(curTac->first == NULL)break;
                    if(!m_funcPropertyGetter->isFuncASimpleExpression(curTac->second->name))break;
                   
                    secondOperands = curTac->second->name;
                    
                    uint prevBlock = backwardGraph[blockId][0];
                    SsaTac* prevTacTail = basicBlocks[prevBlock]->getTacTail();
                    SsaTac* prevTacHead = basicBlocks[prevBlock]->getTacHead();
                    expression = secondOperands + " call";
                    
                    SsaTac* tacTailTail = new SsaTac();
                    tacTailTail->prev = prevTacTail;
                    SsaTac* prevCurTac = tacTailTail;
                    if(prevTacHead != NULL)
                    {
                        do
                        {
                            prevCurTac = prevCurTac->prev;
                            if(prevCurTac->type != TAC_ACTUAL)break;
                            if(prevCurTac->first->type != SYM_INT &&
                                prevCurTac->first->name[0] == 'g')break;
                            
                            expression += " "+ getStringOfSymb(prevCurTac->first);
                        }while(prevCurTac != prevTacHead);
                        if(prevCurTac->type == TAC_ACTUAL &&
                            prevCurTac->first->type != SYM_INT &&
                            prevCurTac->first->name[0] == 'g')break;
                    }
                    
                    it = m_expressTable.find(expression);
                    if(it == m_expressTable.end())
                    {
                        if(!checkTheSymbVar(curTac->first))break;
                       
                        m_expressTable[expression] = curTac->first->name;
                        needToDelete.push_back(expression);
                    }
                    else
                    {
                        string needToReplace = m_expressTable[expression];
                        
                        SsaSymb* copySymb;
                        if(needToReplace.c_str()[0] == 't')
                            copySymb = tName2SsaSymbs[needToReplace];
                        else copySymb = uName2SsaSymbs[needToReplace];
                        curTac->second = copySymb;
                        curTac->third = NULL;
                        addTacToUseListForSsaSymb(curTac,copySymb,curTac->secondPoint);
                        curTac->thirdPoint = NULL;
                        curTac->type = TAC_COPY;
                        m_isOptimize = true;
                        
                        tacTailTail->prev = prevTacTail;
                        SsaTac* prevCurTac = tacTailTail;
                        if(prevTacHead == NULL)break;  
                        do
                        {
                            prevCurTac = prevCurTac->prev;
                            if(prevCurTac->type != TAC_ACTUAL)break;
                            prevCurTac->type = TAC_UNDEF;
                            if(prevCurTac->first->type != SYM_INT &&
                                prevCurTac->first->name[0] != 'g')
                            {
                                prevCurTac->first->useTimes--;
                                deleteUseSsaTac(prevCurTac->firstPoint);
                            }
                        }while(prevCurTac != prevTacHead);
                        basicBlocks[prevBlock]->cleanDirtyTac();
                    }
                break;
                }
                break;
            }
        } while (curTac != tacTail);
        delete tacHeadHead;
    }

        

    for(uint i = 0;i < m_mustPassNodeTree[blockId].size();i++)
    {
        uint sonBlockId = m_mustPassNodeTree[blockId][i];
        deleteCommonExpression(sonBlockId);
    }
    
   
    for(uint i = 0; i < needToDelete.size();i++)
        m_expressTable.erase(needToDelete[i]);
}

bool DelGlobalExpror::checkTheSymbVar(SsaSymb* varSymb)
{
    if(varSymb->type == SYM_INT)return true;
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    unordered_map<string,SsaSymb*>::iterator it;
    if(varSymb->type == SYM_VAR && varSymb->name[0] == 't')
    {
        it = tName2SsaSymbs.find(varSymb->name);
        if(it != tName2SsaSymbs.end())return true;
    }
    if(varSymb->type == SYM_VAR && varSymb->name[0] == 'u')
    {
        it = uName2SsaSymbs.find(varSymb->name);
        if(it != uName2SsaSymbs.end())return true;        
    }
    return false;
}

string DelGlobalExpror::getStringOfSymb(SsaSymb* varSymb)
{
    string varSymbName;
    if(varSymb->type == SYM_INT)
        varSymbName = to_string(varSymb->value);
    else varSymbName = varSymb->name;
    return varSymbName;
}

void DelGlobalExpror::addExpressionIntoTable(SsaTac* curTac,vector<string>& needDeleteList)
{
    string secondOperands,thirdOperands;
    string firstOperands,needSymbol;
    switch (curTac->type)
    {
   
    case TAC_ADD:
    case TAC_MUL:
    case TAC_EQ:
    case TAC_NE:
    case TAC_OR:
    case TAC_AND:
        firstOperands = getStringOfSymb(curTac->first);
        secondOperands = getStringOfSymb(curTac->second);
        thirdOperands = getStringOfSymb(curTac->third);
        needSymbol = m_tacTypeToString[curTac->type];
        m_expressTable[secondOperands + " " + needSymbol
        + " " + thirdOperands] = firstOperands;
        m_expressTable[thirdOperands + " " + needSymbol
        + " " + secondOperands] = firstOperands;
        needDeleteList.push_back(secondOperands + " " 
        + needSymbol + " " + thirdOperands);
        needDeleteList.push_back(thirdOperands + " " 
        + needSymbol + " " + secondOperands);
        break;

    case TAC_SUB:
    case TAC_DIV:
    case TAC_MOD:
    case TAC_LT:
    case TAC_LE:
    case TAC_GT:
    case TAC_GE:
        firstOperands = getStringOfSymb(curTac->first);
        secondOperands = getStringOfSymb(curTac->second);
        thirdOperands = getStringOfSymb(curTac->third);
        needSymbol = m_tacTypeToString[curTac->type];
        m_expressTable[secondOperands + " " + needSymbol
        + " " + thirdOperands] = firstOperands;  
        needDeleteList.push_back(secondOperands + " " 
        + needSymbol + " " + thirdOperands);  
        break;
    case TAC_NEG:
    case TAC_NOT:
        firstOperands = getStringOfSymb(curTac->first);
        secondOperands = getStringOfSymb(curTac->second);
        needSymbol = m_tacTypeToString[curTac->type];
        m_expressTable[secondOperands + " " + needSymbol] = firstOperands; 
        needDeleteList.push_back(secondOperands + " " + needSymbol);
        break;
    case TAC_LEA:
        firstOperands = getStringOfSymb(curTac->first);
        secondOperands = getStringOfSymb(curTac->second);
        thirdOperands = getStringOfSymb(curTac->third);
        needSymbol = m_tacTypeToString[curTac->type];
        m_expressTable[secondOperands + " " + needSymbol
             + " " + thirdOperands] = firstOperands; 
        needDeleteList.push_back(secondOperands + " " + needSymbol
             + " " + thirdOperands);
        break;
    }
}



bool DelGlobalExpror::weakeningTac(SsaTac* curTac)
{
    SsaSymb* firstOperands = curTac->first;
    SsaSymb* secondOperands = curTac->second;
    SsaSymb* thirdOperands = curTac->third;
    switch (curTac->type)
    {
    case TAC_ADD:
       
        if(secondOperands->type == SYM_INT && 
            secondOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->second = curTac->third;
            curTac->secondPoint = curTac->thirdPoint;
            curTac->thirdPoint = NULL; 
            curTac->third = NULL;
            break;
        }
     
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third = NULL;
            break;
        }
        break;
    case TAC_SUB:
        
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third = NULL;
            break;
        }
        break;
    case TAC_MUL:
       
        if(secondOperands->type == SYM_INT && 
            secondOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third->useTimes--;
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->third = NULL;
            break;
        }
        
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            deleteUseSsaTac(curTac->secondPoint);
            curTac->second = NULL;
            break;
        }
        
       if(secondOperands->type == SYM_INT && 
            secondOperands->value == 1)
        {
            curTac->type = TAC_COPY;
            curTac->second = curTac->third;
            curTac->secondPoint = curTac->thirdPoint;
            curTac->third = NULL;           
            curTac->thirdPoint = NULL; 
            break;
        }
        
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 1)
        {
            curTac->type = TAC_COPY;
            curTac->third = NULL;
            break;
        }
        break;
    case TAC_DIV:
       
        if(thirdOperands->type == SYM_VAR && 
            thirdOperands == secondOperands)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = new SsaSymb();
            curTac->second->type = SYM_INT;
            curTac->second->value = 1;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;
        }
        
        if(secondOperands->type == SYM_INT &&
            secondOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third->useTimes--;
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->third = NULL;
            break;
        }
        break;
    case TAC_MOD:
         
        if((thirdOperands->type == SYM_VAR && 
            thirdOperands == secondOperands) || 
            (thirdOperands->type == SYM_INT &&
            thirdOperands->value == 1))
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = new SsaSymb();
            curTac->second->type = SYM_INT;
            curTac->second->value = 0;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            if(thirdOperands->type == SYM_VAR)
                deleteUseSsaTac(curTac->thirdPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;    
        }
        
        if(secondOperands->type == SYM_INT &&
            secondOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third->useTimes--;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;               
        }
        break;
    case TAC_NE:
    case TAC_LT:
    case TAC_GT:
        
        if(thirdOperands->type == SYM_VAR && 
            thirdOperands == secondOperands)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = new SsaSymb();
            curTac->second->type = SYM_INT;
            curTac->second->value = 0;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;            
        }
        break;
    case TAC_LE:
    case TAC_GE:
    case TAC_EQ:
        
        if(thirdOperands->type == SYM_VAR && 
            thirdOperands == secondOperands)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = new SsaSymb();
            curTac->second->type = SYM_INT;
            curTac->second->value = 1;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;            
        }
        break;
    case TAC_OR:
        
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 1)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = curTac->third;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;            
        }
        
        if(secondOperands->type == SYM_INT && 
            secondOperands->value == 1)
        {
            curTac->type = TAC_COPY;
            curTac->third->useTimes--;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->thirdPoint = NULL;
            break;            
        }
        break;
    case TAC_AND:
        
        if(thirdOperands->type == SYM_INT && 
            thirdOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->second->useTimes--;
            curTac->second = curTac->third;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->secondPoint);
            curTac->secondPoint = NULL;
            curTac->thirdPoint = NULL;
            break;            
        }
        
        if(secondOperands->type == SYM_INT && 
            secondOperands->value == 0)
        {
            curTac->type = TAC_COPY;
            curTac->third->useTimes--;
            curTac->third = NULL;
            deleteUseSsaTac(curTac->thirdPoint);
            curTac->thirdPoint = NULL;
            break;            
        }
        break;
    default:
        break;
    }
    if(curTac->type == TAC_COPY)
    {
        m_isOptimize = true;
        return true;
    }
    return false;
}

#endif

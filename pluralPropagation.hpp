#ifndef PLURALPROPAGATION_HPP
#define PLURALPROPAGATION_HPP
#include "globalPolicyExecutor.hpp"

class PluralPropagation:
public GlobalPolicyExecutor
{
private:
    bool m_isOptimize;
private:
    void clear(void);
    void replaceSymb(SsaSymb* &replacer,SsaSymb* &replacee,SsaTac* &needReplaceTac);
    void testOneSymb(string originalName,SsaSymb* &replacer,
    SsaSymb* &replacee,UseSsaTac* &needReplaceUseTac);
public:
    PluralPropagation();
    ~PluralPropagation();
    void printInfoOfOptimizer(void);
    bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter);
};

PluralPropagation::PluralPropagation()
{
    m_name = "复数传播策略器";
}

PluralPropagation::~PluralPropagation()
{

}

void PluralPropagation::clear(void)
{
    m_isOptimize = false;
    m_block = NULL;
}

void PluralPropagation::printInfoOfOptimizer(void)
{

}

bool PluralPropagation::runOptimizer(FunctionBlock* block,
    FuncPropertyGetter* funcPropertyGetter)
{
    clear();
    m_block = block;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
   
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    if(uName2SsaSymbs.size() + tName2SsaSymbs.size() == 0)return m_isOptimize;
  
    unordered_set<SsaSymb*> SsaSymbsSet;
    unordered_map<string,SsaSymb*>::iterator it;
    SsaSymbsSet.clear();
    for(it = uName2SsaSymbs.begin();it != uName2SsaSymbs.end();it++)SsaSymbsSet.insert(it->second);
    for(it = tName2SsaSymbs.begin();it != tName2SsaSymbs.end();it++)SsaSymbsSet.insert(it->second);
    
    for(it = uName2SsaSymbs.begin();it != uName2SsaSymbs.end();it++)
    {
        SsaTac* curTac = (it->second)->defPoint;
        if(curTac->type != TAC_INSERT)continue;
        bool needTurnCopy = true;
        SsaSymb* curSymb = curTac->functionSymb[0];
        UseSsaTac* curSymbUse = curTac->functionSymb2Tac[0];
        for(uint i = 0;i < curTac->functionSymb.size();i++)
        {
            if(curSymb != curTac->functionSymb[i])
                needTurnCopy = false;
        }
        if(!needTurnCopy)continue;
        
        if(curSymb->type == SYM_VAR && curSymb->name[0] == 'u')
        {
            if(uName2SsaSymbs.find(curSymb->name) == uName2SsaSymbs.end())
            {   
                
                
            }
        }
        for(uint i = 0;i < curTac->functionSymb.size();i++)
        {
            curTac->functionSymb[i] = NULL;
            curTac->functionSymb2Tac[i] = NULL;
        }
        curTac->type = TAC_COPY;
        curTac->second = curSymb;
        curTac->secondPoint = curSymbUse;
    }
    vector<SsaSymb*> copyTacSsaSymbs;
    vector<string> needDeleteSymbs;
    copyTacSsaSymbs.clear();
    needDeleteSymbs.clear();
    it = uName2SsaSymbs.begin();
    for(;it != uName2SsaSymbs.end();it++)
    {
        SsaTac* curTac = (it->second)->defPoint;
        if(curTac->type != TAC_COPY)continue;
        if(curTac->second->type != SYM_VAR)continue;
        unordered_set<SsaSymb*>::iterator iter;
        iter = SsaSymbsSet.find(curTac->second);
        if(iter == SsaSymbsSet.end())continue;
        copyTacSsaSymbs.push_back(it->second);
        needDeleteSymbs.push_back(it->first);
    }

    it = tName2SsaSymbs.begin();
    for(;it != tName2SsaSymbs.end();it++)
    {
        SsaTac* curTac = (it->second)->defPoint;
        if(curTac->type != TAC_COPY)continue;
        if(curTac->second->type != SYM_VAR)continue;
        unordered_set<SsaSymb*>::iterator iter;
        iter = SsaSymbsSet.find(curTac->second);
        if(iter == SsaSymbsSet.end())continue;
        copyTacSsaSymbs.push_back(it->second);
        needDeleteSymbs.push_back(it->first);
    }

    
    for(uint i = 0;i < copyTacSsaSymbs.size();i++)
    {
        SsaSymb* replaceeSymb = copyTacSsaSymbs[i];
        SsaTac* curTac = replaceeSymb->defPoint;
        SsaSymb* replacerSymb = curTac->second;   
        
        UseSsaTac* useTac = replaceeSymb->useList;
        while(useTac->next != NULL)
        {
            SsaTac* needReplaceTac = useTac->next->code;
            
            replaceSymb(replacerSymb,replaceeSymb,needReplaceTac);
            useTac = useTac->next;
        }
    }
    for(uint i = 0;i < copyTacSsaSymbs.size();i++)
    {
        SsaSymb* replaceeSymb = copyTacSsaSymbs[i];
        SsaTac* curTac = replaceeSymb->defPoint;
        curTac->second->useTimes--;
        deleteUseSsaTac(curTac->secondPoint);
        curTac->type = TAC_UNDEF;        
    }
    for(uint i = 0;i < basicBlocks.size();i++)
    {
        basicBlocks[i]->cleanDirtyTac();
    }
    for(uint i = 0;i < needDeleteSymbs.size();i++)
    {
        if(needDeleteSymbs[i].c_str()[0] == 't')
            tName2SsaSymbs.erase(needDeleteSymbs[i]);
        else uName2SsaSymbs.erase(needDeleteSymbs[i]);
    }
    return m_isOptimize;
}


void PluralPropagation::replaceSymb(SsaSymb* &replacer,
        SsaSymb* &replacee,SsaTac* &needReplaceTac)
{
    m_isOptimize = true;
    switch (needReplaceTac->type)
    {
    case TAC_INSERT:
        for(uint i = 0;i < needReplaceTac->functionSymb.size();i++)
        {
            if(replacee != needReplaceTac->functionSymb[i])continue;
            needReplaceTac->functionSymb[i] = replacer;
            
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->functionSymb2Tac[i]);
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
        if(replacee == needReplaceTac->second)
        {
            needReplaceTac->second = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->secondPoint);            
        }
        if(replacee == needReplaceTac->third)
        {
            needReplaceTac->third = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->thirdPoint);            
        }
        break;
    case TAC_NEG:
    case TAC_POSI:
    case TAC_NOT:
    case TAC_COPY:
        if(replacee == needReplaceTac->second)
        {
            needReplaceTac->second = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->secondPoint);            
        }
        break;
    case TAC_ARR_L:

        if(replacee == needReplaceTac->second)
        {
            needReplaceTac->second = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->secondPoint);            
        }        
        if(replacee == needReplaceTac->third)
        {
            needReplaceTac->third = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->thirdPoint);            
        }        
        break;
    case TAC_ARR_R:
    case TAC_LEA:
        if(replacee == needReplaceTac->third)
        {
            needReplaceTac->third = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->thirdPoint);            
        }
        break;        
    case TAC_IFZ:
    case TAC_ACTUAL:  
        if(replacee == needReplaceTac->first)
        {
            needReplaceTac->first = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->firstPoint);            
        }      
        break;
    case TAC_RETURN:
        if(needReplaceTac->first == NULL)break;
        if(replacee == needReplaceTac->first)
        {
            needReplaceTac->first = replacer;
            addTacToUseListForSsaSymb(needReplaceTac,replacer,
            needReplaceTac->firstPoint);            
        }             
        break;
    default:
        break;   
    } 
}
#endif
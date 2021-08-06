

#ifndef CONDCONSTPROPAGATION_HPP
#define CONDCONSTPROPAGATION_HPP
#include <queue>
#include "globalPolicyExecutor.hpp"

#define UNKNOW 0 	
#define ASKNOW 1 	
#define UPKNOW 2 	


class CondConstPropagation:
public GlobalPolicyExecutor
{
private:
    vector<bool> m_isBlockUseful;            
    vector<uint> m_isVarValueKnow;           
    vector<int> m_assignVarValue;             
    queue<uint> m_blockWorkList;             
    unordered_map<string,uint> m_var2id;      
    unordered_map<uint,string> m_id2var;      
    unordered_set<uint> m_varIdWorkList;      
private:
    void clear();
    void addToBlockWorkList(uint blockId);    
    void addToVarIdWorkListA(string&          
        varName,int value);
    void addToVarIdWorkListU(string& varName);
    void actionOfTwoOperands(SsaTac* tacNode);
    void actionOfOneOperand(SsaTac* tacNode);
    void actionOfInsertOperand(SsaTac* tacNode);
    void actionOfMemOrCall(SsaTac* tacNode);
    void actionOfIfz(SsaTac* tacNode);
    void actionToOneTac(SsaTac* tacNode);
    void VarPropagation(void);          
    void ReplaceVarUseConst(SsaSymb* varSymb,int value); 
    void ReplaceVarAndCleanUseTac(SsaSymb* &deleteSymb,
        SsaSymb* &varSymb,UseSsaTac* &useTac,int value);      
    void deleteUnuseBlock(void);
public:
    void printInfoOfOptimizer(void);
    bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter);
    CondConstPropagation();
    ~CondConstPropagation();
};


void CondConstPropagation::clear()
{
    m_isBlockUseful.clear();
    m_isVarValueKnow.clear();
    m_assignVarValue.clear();
    m_block = NULL;
    while(!m_blockWorkList.empty())
        m_blockWorkList.pop();
    m_var2id.clear();
    m_id2var.clear();
    m_varIdWorkList.clear();
}

CondConstPropagation::CondConstPropagation()
{
    m_name = "常数传播删除器";
    clear();
}

CondConstPropagation::~CondConstPropagation()
{
}

bool CondConstPropagation::runOptimizer(FunctionBlock* block,
    FuncPropertyGetter* funcPropertyGetter)
{
    clear();
    m_block = block;
    uint varCnt = 0;
    vector<BasicBlock*>& basicBlocks = m_block->getBasicBlocks();
    m_isBlockUseful.resize(basicBlocks.size());
    for(uint i = 0;i < m_isBlockUseful.size();i++)m_isBlockUseful[i] = false;
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    if(uName2SsaSymbs.size() + tName2SsaSymbs.size() == 0)return false;
    m_assignVarValue.resize(uName2SsaSymbs.size() + tName2SsaSymbs.size());
    for(uint i = 0;i < m_assignVarValue.size();i++)m_isVarValueKnow.push_back(UNKNOW);
    unordered_map<string,SsaSymb*>::iterator it;
    unordered_map<string,uint>::iterator iter;
    for(it = uName2SsaSymbs.begin();it != uName2SsaSymbs.end();it++)m_var2id[it->first]=varCnt++;
    for(it = tName2SsaSymbs.begin();it != tName2SsaSymbs.end();it++)m_var2id[it->first]=varCnt++;
    for(iter = m_var2id.begin();iter!=m_var2id.end();iter++)m_id2var[iter->second] = iter->first;

    addToBlockWorkList(0);
    while(!m_blockWorkList.empty() || !m_varIdWorkList.empty())
    {
        while(!m_blockWorkList.empty())
        {
            uint blockId = m_blockWorkList.front();
            m_blockWorkList.pop();
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
                actionToOneTac(curTac);
            } while (curTac != tacTail);
        }
        
        while(!m_varIdWorkList.empty())
        {
            unordered_set<uint>::iterator it = 
                m_varIdWorkList.begin();
            uint curIdOfVar = *it;
            m_varIdWorkList.erase(*it);
            SsaSymb* curVar;
            if(m_id2var[curIdOfVar].c_str()[0] == 't')
                curVar = tName2SsaSymbs[m_id2var[curIdOfVar]];
            else curVar = uName2SsaSymbs[m_id2var[curIdOfVar]];
            UseSsaTac* curUseTac = curVar->useList;
            while(curUseTac->next != NULL)
            {
                actionToOneTac(curUseTac->next->code);
                curUseTac = curUseTac->next;
            }
        }
    }
    bool isOptimize = false;
    for(uint i = 0;i < m_isVarValueKnow.size();i++)
    {
        if(m_isVarValueKnow[i] != ASKNOW)continue;
        isOptimize = true;
    }
    for(uint i = 0;i < m_isBlockUseful.size();i++)
    {
        if(m_isBlockUseful[i] == true)continue;
        isOptimize = true;
    }    
    
    VarPropagation();

    for(uint i = 0;i < basicBlocks.size();i++)
        basicBlocks[i]->cleanDirtyTac();

    for(uint i = 0;i < m_isVarValueKnow.size();i++)
    {
        if(m_isVarValueKnow[i] != ASKNOW)continue;
        string varName = m_id2var[i];
        if(varName.c_str()[0] == 't')tName2SsaSymbs.erase(varName);
        else uName2SsaSymbs.erase(varName);
    }
    deleteUnuseBlock();
    return isOptimize;
}

void CondConstPropagation::printInfoOfOptimizer(void)
{
    
    cout << "删掉的基本块有：" << endl;
    for(uint i = 0;i < m_isBlockUseful.size();i++)
    {
        if(m_isBlockUseful[i] == false)
        {
            cout << "B" << i << "\t";
        }   
    }
    cout << endl;
    cout << "常数传播后：" << endl;
    for(uint i = 0;i < m_isVarValueKnow.size();i++)
    {
        if(m_isVarValueKnow[i] == ASKNOW)
        {
            cout << "变量 " << m_id2var[i] << " : " << 
                m_assignVarValue[i] << endl;
        }
    }
}

void CondConstPropagation::actionToOneTac(SsaTac* tacNode)
{
    switch (tacNode->type)
    {
    case TAC_INSERT:
        actionOfInsertOperand(tacNode);
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
        actionOfTwoOperands(tacNode);
        break;
    case TAC_NEG:
    case TAC_POSI:
    case TAC_NOT:
    case TAC_COPY:
        actionOfOneOperand(tacNode);
        break;
    case TAC_FORMAL:
        actionOfMemOrCall(tacNode);
        break;
    case TAC_CALL:
        if(tacNode->first != NULL)
            actionOfMemOrCall(tacNode);
        break;
    case TAC_ARR_R:
        actionOfMemOrCall(tacNode);
        break;
    case TAC_IFZ:
        actionOfIfz(tacNode);
        break;
    default:
        break;
    }    
}

void CondConstPropagation::addToBlockWorkList(uint blockId)
{
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    if(m_isBlockUseful[blockId] == true)return;
    uint uniqueSuccBlockId = blockId;
    while(forwardGraph[uniqueSuccBlockId].size() == 1)
    {
        m_isBlockUseful[uniqueSuccBlockId] = true;
        m_blockWorkList.push(uniqueSuccBlockId);
        uniqueSuccBlockId = forwardGraph[uniqueSuccBlockId][0];
    }
    m_isBlockUseful[uniqueSuccBlockId] = true;
    m_blockWorkList.push(uniqueSuccBlockId);
}


void CondConstPropagation::addToVarIdWorkListA(string& varName,int value)
{
    uint idOfVar = m_var2id[varName];
    m_assignVarValue[idOfVar] = value;
    if(m_isVarValueKnow[idOfVar] == UNKNOW)
        m_varIdWorkList.insert(idOfVar);
    m_isVarValueKnow[idOfVar] = ASKNOW;
}

void CondConstPropagation::addToVarIdWorkListU(string& varName)
{
    uint idOfVar = m_var2id[varName];
    if(m_isVarValueKnow[idOfVar] == ASKNOW)
        m_varIdWorkList.insert(idOfVar);
    m_isVarValueKnow[idOfVar] = UPKNOW;
        
}

void CondConstPropagation::actionOfTwoOperands(SsaTac* tacNode)
{
    string firstOperand(tacNode->first->name);
    unordered_map<string,uint>::iterator it;
    it = m_var2id.find(firstOperand);
    if(it == m_var2id.end())return;
   
    if(tacNode->second->type == SYM_VAR)
    {
        string secondOperand(tacNode->second->name);
        it = m_var2id.find(secondOperand);
        if(it == m_var2id.end())
        {
            addToVarIdWorkListU(firstOperand);
            return;
        }
        uint idOfSecondVar = m_var2id[secondOperand];
        if(m_isVarValueKnow[idOfSecondVar] != ASKNOW)
        {
            addToVarIdWorkListU(firstOperand);
            return;       
        }
    }

    if(tacNode->third->type == SYM_VAR)
    {
        string thirdOperand(tacNode->third->name);
        it = m_var2id.find(thirdOperand);
        if(it == m_var2id.end())
        {
            addToVarIdWorkListU(firstOperand);
            return;
        }
        uint idOfThirdVar = m_var2id[thirdOperand];
        if(m_isVarValueKnow[idOfThirdVar] != ASKNOW)
        {
            addToVarIdWorkListU(firstOperand);
            return;       
        }
    }
    
    int secondValue,thirdValue,firstValue;
    string secondOperand(tacNode->second->name);
    string thirdOperand(tacNode->third->name);
    if(tacNode->second->type == SYM_INT)
        secondValue = tacNode->second->value;
    else 
    {
        uint idOfSecondVar = m_var2id[secondOperand];
        secondValue = m_assignVarValue[idOfSecondVar];
    }
    if(tacNode->third->type == SYM_INT)
        thirdValue = tacNode->third->value;
    else 
    {
        uint idOfThirdVar = m_var2id[thirdOperand];
        thirdValue = m_assignVarValue[idOfThirdVar];
    }
    switch (tacNode->type)
    {
    case TAC_ADD:
        firstValue = secondValue + thirdValue;
        break;
    case TAC_SUB:
        firstValue = secondValue - thirdValue;
        break;
    case TAC_MUL:
        firstValue = secondValue * thirdValue;
        break;
    case TAC_DIV:
        firstValue = secondValue / thirdValue;
        break;
    case TAC_EQ:
        firstValue = secondValue == thirdValue;
        break;
    case TAC_MOD:
        firstValue = secondValue % thirdValue;
        break;
    case TAC_NE:
        firstValue = secondValue != thirdValue;
        break;
    case TAC_LT:
        firstValue = secondValue < thirdValue;
        break;
    case TAC_LE:
        firstValue = secondValue <= thirdValue;
        break;
    case TAC_GT:
        firstValue = secondValue > thirdValue;
        break;
    case TAC_GE:
        firstValue = secondValue >= thirdValue;
        break;
    case TAC_OR:
        firstValue = secondValue || thirdValue;
        break;
    case TAC_AND:
        firstValue = secondValue && thirdValue;
        break;
    default:
        exit(-1);
        break;
    }
    addToVarIdWorkListA(firstOperand,firstValue);

}

void CondConstPropagation::actionOfOneOperand(SsaTac* tacNode)
{
    string firstOperand(tacNode->first->name);
    unordered_map<string,uint>::iterator it;
    it = m_var2id.find(firstOperand);
    if(it == m_var2id.end())return;
 
    if(tacNode->second->type == SYM_VAR)
    {
        string secondOperand(tacNode->second->name);
        it = m_var2id.find(secondOperand);
        if(it == m_var2id.end())
        {
            addToVarIdWorkListU(firstOperand);
            return;
        }
        uint idOfSecondVar = m_var2id[secondOperand];
        if(m_isVarValueKnow[idOfSecondVar] != ASKNOW)
        {
            addToVarIdWorkListU(firstOperand);
            return;       
        }
    }
    int secondValue,firstValue;
    string secondOperand(tacNode->second->name);
    if(tacNode->second->type == SYM_INT)
        secondValue = tacNode->second->value;
    else 
    {
        uint idOfSecondVar = m_var2id[secondOperand];
        secondValue = m_assignVarValue[idOfSecondVar];
    } 
    switch (tacNode->type)
    {
    case TAC_NEG:
        firstValue = - secondValue;
        break;
    case TAC_POSI:
    case TAC_COPY:
        firstValue = secondValue;
        break;
    case TAC_NOT:
        firstValue = !secondValue;
        break;
    default:
        exit(-1);
        break;
    }
    addToVarIdWorkListA(firstOperand,firstValue);
}

void CondConstPropagation::actionOfInsertOperand(SsaTac* tacNode)
{
  
    string firstOperand(tacNode->first->name);
    vector<vector<uint>>& backwardGraph = m_block->getBackwardGraph();
    vector<SsaSymb*>& insertVar = tacNode->functionSymb;
    unordered_set<string> insertEffectVar;
    unordered_set<string> insertEffectNoZeroVar;
    vector<int> constRecordor;
    constRecordor.clear();
    insertEffectVar.clear();
    insertEffectNoZeroVar.clear();
    uint blockId = tacNode->blockId;
    for(uint i = 0;i < backwardGraph[blockId].size();i++)
    {
        if(!m_isBlockUseful[backwardGraph[blockId][i]])continue;
        if(insertVar[i]->type == SYM_INT)constRecordor.push_back(insertVar[i]->value);
        if(insertVar[i]->type != SYM_VAR)continue;
            insertEffectVar.insert(insertVar[i]->name);
    }
  
    unordered_set<string>::iterator it;;
    for(it = insertEffectVar.begin();it != insertEffectVar.end();++it)
    {
        if((*it).c_str()[0] != 'u')
        {
            insertEffectNoZeroVar.insert(*it);
            continue;
        }
        uint filePathLen = (*it).size();
        uint dPosition = (*it).find('d');
        const char* cFilepath = (*it).c_str()+dPosition+1;
        uint needTestId = atoi(cFilepath);
        if(needTestId != 0)insertEffectNoZeroVar.insert(*it);
    }
   
    if(insertEffectNoZeroVar.size() == 0)return;
   
    bool isEqualAndConst = true;
    for(it = insertEffectNoZeroVar.begin();it != insertEffectNoZeroVar.end();it++)
    {
        uint idOfVar = m_var2id[*it];
        if(m_isVarValueKnow[idOfVar] != ASKNOW)
        {
            isEqualAndConst = false;
            break;
        }
    }  
    if(isEqualAndConst == false)
    {
        addToVarIdWorkListU(firstOperand);
        return;
    }
    it = insertEffectNoZeroVar.begin();
    uint idOfVar = m_var2id[*it];
  
    int firstvalue = m_assignVarValue[idOfVar];
    for(it = insertEffectNoZeroVar.begin();it != insertEffectNoZeroVar.end();it++)
    {
        uint idOfVar = m_var2id[*it];
        if(m_assignVarValue[idOfVar] != firstvalue)
        {
            isEqualAndConst = false;
            break;
        }
    }
    for(uint i = 0;i < constRecordor.size();i++)   
    {
        if(constRecordor[i] != firstvalue)
        {
            isEqualAndConst = false;
            break;            
        }
    } 

    if(isEqualAndConst == false)
    {
        addToVarIdWorkListU(firstOperand);
        return;
    }
    addToVarIdWorkListA(firstOperand,firstvalue);
}

void CondConstPropagation::actionOfMemOrCall(SsaTac* tacNode)
{
    
    string firstOperand(tacNode->first->name);
    unordered_map<string,uint>::iterator it;
    it = m_var2id.find(firstOperand);
    if(it == m_var2id.end())return;
   
    addToVarIdWorkListU(firstOperand);
}

void CondConstPropagation::actionOfIfz(SsaTac* tacNode)
{
    vector<vector<uint>>& forwardGraph = m_block->getForwardGraph();
    uint blockId = tacNode->blockId;
    uint firstBid = forwardGraph[blockId][0];
    uint secondBid = forwardGraph[blockId][1];
    uint gotoBid = atoi(tacNode->second->name+1);
    uint succBid = firstBid == gotoBid?secondBid:firstBid;
    if(tacNode->first->type == SYM_INT)
    {
        int value = tacNode->first->value;
        if(value != 0)addToBlockWorkList(succBid);
        else addToBlockWorkList(gotoBid);
        return;
    }
    else if(tacNode->first->type == SYM_VAR)
    {
        string firstOperand(tacNode->first->name);
        unordered_map<string,uint>::iterator it;
        it = m_var2id.find(firstOperand);
        if(it == m_var2id.end())
        {
            addToBlockWorkList(succBid);
            addToBlockWorkList(gotoBid);
            return;
        }
        uint idOfFirstVar = m_var2id[firstOperand];
        if(m_isVarValueKnow[idOfFirstVar] == ASKNOW)
        {
            int value = m_assignVarValue[idOfFirstVar];
            if(value != 0)addToBlockWorkList(succBid);
            else addToBlockWorkList(gotoBid);
            return;            
        }
        addToBlockWorkList(succBid);
        addToBlockWorkList(gotoBid);
    }
    else
    {
        exit(-1);
    }
}


void CondConstPropagation::VarPropagation(void)
{
    
    vector<SsaSymb*> needDeleteVarList;
    vector<int> needReplaceValueList;
    needDeleteVarList.clear();
    unordered_map<string,SsaSymb*>& uName2SsaSymbs = m_block->getUName2SsaSymbs();
    unordered_map<string,SsaSymb*>& tName2SsaSymbs = m_block->getTName2SsaSymbs();
    for(uint i = 0;i < m_isVarValueKnow.size();i++)
    {
        if(m_isVarValueKnow[i] != ASKNOW)continue;
        string varName = m_id2var[i];
        SsaSymb* varSymb;
        if(varName.c_str()[0] == 't')varSymb = tName2SsaSymbs[varName];
        else varSymb = uName2SsaSymbs[varName];
        needDeleteVarList.push_back(varSymb);
        needReplaceValueList.push_back(m_assignVarValue[i]);
    }    
    
    for(uint i = 0;i < needDeleteVarList.size();i++)
    {
        SsaSymb* needDeleteVar = needDeleteVarList[i];
        ReplaceVarUseConst(needDeleteVar,needReplaceValueList[i]);
    }
    for(uint i = 0;i < needDeleteVarList.size();i++)
    {
        SsaSymb* needDeleteVar = needDeleteVarList[i];
        needDeleteVar->defPoint->type = TAC_UNDEF;
    }
}   

void CondConstPropagation::ReplaceVarUseConst(SsaSymb* varSymb,int value)
{
    UseSsaTac* varUseListHead = varSymb->useList;
    while(varUseListHead->next != NULL)
    {
        SsaTac* needReplaceTac = varUseListHead->next->code;
        switch (needReplaceTac->type)
        {
        case TAC_INSERT:
            for(uint i = 0;i < needReplaceTac->functionSymb.size();i++)
            {
                ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->functionSymb[i],
                    needReplaceTac->functionSymb2Tac[i],value);                
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
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->second,
                needReplaceTac->secondPoint,value);
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->third,
                needReplaceTac->thirdPoint,value);            
            break;
        case TAC_NEG:
        case TAC_POSI:
        case TAC_NOT:
        case TAC_COPY:
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->second,
                needReplaceTac->secondPoint,value);            
            break;
        case TAC_IFZ:
        case TAC_ACTUAL:
        case TAC_RETURN:
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->first,
                needReplaceTac->firstPoint,value);
            break;
        case TAC_ARR_L:
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->second,
                needReplaceTac->secondPoint,value);
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->third,
                needReplaceTac->thirdPoint,value);             
            break;
        case TAC_ARR_R:
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->first,
                needReplaceTac->firstPoint,value);
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->third,
                needReplaceTac->thirdPoint,value); 
            break;
        case TAC_LEA:
            ReplaceVarAndCleanUseTac(varSymb,needReplaceTac->third,
                needReplaceTac->thirdPoint,value); 
            break;
        default:
            break;
        }
        varUseListHead = varUseListHead->next;
    }
}

void CondConstPropagation::ReplaceVarAndCleanUseTac(
SsaSymb* &deleteSymb,SsaSymb* &varSymb,UseSsaTac* &useTac,int value)
{
    string deleteVarName(deleteSymb->name);
    if(varSymb->type == SYM_INT)return;
    if(varSymb->type == SYM_VAR)
    {
        string varSumbName(varSymb->name);
        if(!deleteVarName.compare(varSumbName))
        {
            varSymb = new SsaSymb();
            varSymb->type = SYM_INT;
            varSymb->value = value;
            useTac = NULL;
        }
    }
}

void CondConstPropagation::deleteUnuseBlock(void)
{
    vector<uint> needDeleteBidList;
    needDeleteBidList.clear();
    for(uint i = 0;i < m_isBlockUseful.size();i++)
    {
        if(m_isBlockUseful[i] == true)continue;
        needDeleteBidList.push_back(i);
    }
    if(needDeleteBidList.size() == 0)return;
   
    m_block->deleteBasicBlock(needDeleteBidList);    
}
#endif
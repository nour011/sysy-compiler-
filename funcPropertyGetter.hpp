
#ifndef FUNCPROPERTYGETTER_HPP
#define FUNCPROPERTYGETTER_HPP
#include <unordered_set>
#include "functionBlock.hpp"


class FuncInfoContainer
{
private:
    string m_funcName;
   
    vector<string> m_callFuncParaList;

    unordered_map<string,uint> m_arrFormalIndex;
    unordered_map<string,vector<pair<uint,uint>>> m_funcFormal2formaled;
    unordered_map<string,vector<pair<string,uint>>> m_funcGlobal2formaled;

    unordered_set<string> m_callFuncList;
    unordered_set<string> m_modifyGlobalName;
    unordered_set<string> m_modifyFormalPointerName;
    unordered_set<string> m_modifyGlobalPointerName;
public:
    void clear(void);
    void addModifyGlobalName(string varName);
    void addModifyGlobalPointerName(string varName);
    void addCallFunc(string funcName);
    void addCallFuncOfLocalArr(string funcName,uint formalVar,uint formaledVar);
    void addCallFuncOfGlobalArr(string funcName,string formalVar,uint formaledVar);
    void printCallFun(void);
    string getFuncName(void){return m_funcName;}
    unordered_set<string>& getCallFuncList(void){return m_callFuncList;};
    unordered_set<string>& getModifyGlobalName(void);
    unordered_set<string>& getModifyGlobalPointerName(void);
    unordered_map<string,uint>& getArrFormalIndex(void){return m_arrFormalIndex;};
    unordered_map<string,vector<pair<uint,uint>>>& getFuncFormal2formaled(void){return m_funcFormal2formaled;};
    unordered_map<string,vector<pair<string,uint>>>& getFuncGlobal2formaled(void){return m_funcGlobal2formaled;};
    FuncInfoContainer(){};
    FuncInfoContainer(string funcName){m_funcName = funcName;};
    ~FuncInfoContainer(){};
};
void FuncInfoContainer::clear(void)
{
    m_callFuncList.clear();
    m_callFuncParaList.clear();
    m_modifyGlobalName.clear();
    m_arrFormalIndex.clear();
    m_funcFormal2formaled.clear();
    m_modifyFormalPointerName.clear();
    m_modifyGlobalPointerName.clear();
}
void FuncInfoContainer::addModifyGlobalName(string varName)
{
    m_modifyGlobalName.insert(varName);
}

void FuncInfoContainer::addModifyGlobalPointerName(string varName)
{
    m_modifyGlobalPointerName.insert(varName);
}

void FuncInfoContainer::addCallFunc(string funcName)
{
    m_callFuncList.insert(funcName);
}
unordered_set<string>& FuncInfoContainer::getModifyGlobalName(void)
{
    return m_modifyGlobalName;
}

unordered_set<string>& FuncInfoContainer::getModifyGlobalPointerName(void)
{
    return m_modifyGlobalPointerName;
}

void FuncInfoContainer::addCallFuncOfLocalArr(string funcName,uint formalVar,uint formaledVar)//局部变量
{
    pair<uint,uint> needAddVar = make_pair(formalVar,formaledVar);
    auto it = m_funcFormal2formaled.find(funcName);
    if(it != m_funcFormal2formaled.end())
    {
        m_funcFormal2formaled[funcName].push_back(needAddVar);
        return;
    }
    vector<pair<uint,uint>> newVector;
    newVector.clear();
    newVector.push_back(needAddVar);
    m_funcFormal2formaled[funcName] = newVector;
    return;
}

void FuncInfoContainer::addCallFuncOfGlobalArr(string funcName,string formalVar,uint formaledVar)//全局变量
{
    pair<string,uint> needAddVar = make_pair(formalVar,formaledVar);
    auto it = m_funcGlobal2formaled.find(funcName);
    if(it != m_funcGlobal2formaled.end())
    {
        m_funcGlobal2formaled[funcName].push_back(needAddVar);
        return;
    }
    vector<pair<string,uint>> newVector;
    newVector.clear();
    newVector.push_back(needAddVar);
    m_funcGlobal2formaled[funcName] = newVector;
    return;
}

void FuncInfoContainer::printCallFun(void)
{
    cout<< endl << "函数内参数传参：" << endl;
    for(auto it = m_funcFormal2formaled.begin();it != m_funcFormal2formaled.end();it++)
    {
        cout << it->first << "\t";
        vector<pair<uint,uint>> formal2formaled = it->second;
        for(uint i = 0;i < formal2formaled.size();i++)
        {
            cout << " (" << formal2formaled[i].first << "," << formal2formaled[i].second << ") ";
        }
        cout << endl;
    }
    cout<< endl << "全局数组参数传参：" << endl;
    for(auto it = m_funcGlobal2formaled.begin();it != m_funcGlobal2formaled.end();it++)
    {
        cout << it->first << "\t";
        vector<pair<string,uint>> global2formaled = it->second;
        for(uint i = 0;i < global2formaled.size();i++)
        {
            cout << " (" << global2formaled[i].first << "," << global2formaled[i].second << ") ";
        }
        cout << endl;
    }
}

class FuncPropertyGetter
{
private:
    vector<vector<uint>> m_backwardGraph;
    unordered_map<string,FuncInfoContainer*> m_funcInfoContainers;
    unordered_set<string> m_funcNameSet;
    unordered_map<string,uint> m_funcName2index;
    unordered_map<uint,string> m_index2funcName;
    unordered_map<string,bool> m_funcSimpleExprFlag;
private:
    void getFuncInfo(FunctionBlock* funcBlock);
    void buildCallGraph(void);
    bool ifArrParameter(SsaTac* codeTac,string& varName);
    string lookForFuncName(BasicBlock* basicBlock);
    void lowWorksheetAlgorithm(void);
    void highWorksheetAlgorithm(void);
public:
    FuncPropertyGetter();
    ~FuncPropertyGetter(){};
    void clear(void);
    void addANewFunc(FunctionBlock* funcBlock);
    bool isFuncASimpleExpression(string funcName);
    unordered_set<string> getDirtyArrName(void);

};

FuncPropertyGetter::FuncPropertyGetter()
{
    clear();
}
void FuncPropertyGetter::clear(void)
{
    m_funcNameSet.clear();
    m_index2funcName.clear();
    m_funcName2index.clear();
    m_funcSimpleExprFlag.clear();
    m_funcInfoContainers.clear();
    m_backwardGraph.clear();
}

void FuncPropertyGetter::addANewFunc(FunctionBlock* funcBlock)
{
    getFuncInfo(funcBlock);
    unordered_set<string> formalVarName;
    vector<BasicBlock*>& basicBlock = funcBlock->getBasicBlocks();
    formalVarName.clear();
    m_funcSimpleExprFlag[funcBlock->m_name] = true;
    for(uint blockId = 0;blockId < basicBlock.size();blockId++)
    {
        if(m_funcSimpleExprFlag[funcBlock->m_name] == false)break;
        SsaTac* tacHead = basicBlock[blockId]->getTacHead();
        SsaTac* tacTail = basicBlock[blockId]->getTacTail();
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
                if(curTac->first->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                if(curTac->second->type != SYM_INT && 
                    curTac->second->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                if(curTac->third->type != SYM_INT && 
                    curTac->third->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                
                break;
            case TAC_NEG:
            case TAC_POSI:
            case TAC_NOT:
            case TAC_COPY:
                if(curTac->first->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                if(curTac->second->type != SYM_INT && 
                    curTac->second->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                break;
            case TAC_CALL:
                m_funcSimpleExprFlag[funcBlock->m_name] == false;
                break;
            case TAC_IFZ:
                if(curTac->first->type != SYM_INT &&
                    curTac->first->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                break;
            case TAC_RETURN:
                if( curTac->first != NULL &&
                    curTac->first->type != SYM_INT &&
                    curTac->first->name[0] == 'g')
                {
                    m_funcSimpleExprFlag[funcBlock->m_name] = false;
                    break;
                }
                break;
            case TAC_ARR_L:
                m_funcSimpleExprFlag[funcBlock->m_name] = false;
                break;
            case TAC_ARR_R:

                m_funcSimpleExprFlag[funcBlock->m_name] = false;
                break;
            default:
                break;
            }
        } while (curTac != tacTail);
        
    }
} 
 
bool FuncPropertyGetter::isFuncASimpleExpression(string funcName)
{
   
    auto it = m_funcSimpleExprFlag.find(funcName);
    if(it == m_funcSimpleExprFlag.end())return false;
    else return m_funcSimpleExprFlag[funcName];
}




void FuncPropertyGetter::getFuncInfo(FunctionBlock* funcBlock)
{
    string funcName = funcBlock->m_name;
    if(m_funcNameSet.find(funcName) == m_funcNameSet.end())
    {
        m_funcNameSet.insert(funcName);
        m_index2funcName[m_funcName2index.size()] = funcName;
        m_funcName2index[funcName] = m_funcName2index.size();
    }
    
    auto funcIterator= m_funcInfoContainers.find(funcName);
    FuncInfoContainer *funcInfo;
    if(funcIterator == m_funcInfoContainers.end())
    {
        funcInfo = new FuncInfoContainer(funcName);
        m_funcInfoContainers[funcName] = funcInfo;
    }
    else funcInfo = funcIterator->second;
    funcInfo->clear();
    
    vector<BasicBlock*>& basicBlock = funcBlock->getBasicBlocks();
    vector<vector<uint>>& forwardGraph = funcBlock->getForwardGraph();
    unordered_set<string>& modifyGlobalPointerName = funcInfo->getModifyGlobalPointerName();
    unordered_map<string,uint>& arrFormalIndex = funcInfo->getArrFormalIndex();
    uint formalNum = 0;
    for(uint blockId = 0;blockId < basicBlock.size();blockId++)
    {
        SsaTac* tacHead = basicBlock[blockId]->getTacHead();
        SsaTac* tacTail = basicBlock[blockId]->getTacTail();
        if(tacHead == NULL)continue;
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead;
        do
        {
            curTac = curTac->next;
            switch(curTac->type)
            {
            case TAC_FORMAL:
                if(curTac->first->type == SYM_ARRAY)
                    arrFormalIndex[curTac->first->name] = formalNum;
                formalNum++;
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
            case TAC_COPY:
            case TAC_ARR_R:
            case TAC_LEA:
                if(curTac->first->name[0] != 'g')break;
                funcInfo->addModifyGlobalName(curTac->first->name);
                break;
            case TAC_CALL:
                if(curTac->first == NULL)break;
                if(curTac->first->name[0] != 'g')break;
                funcInfo->addModifyGlobalName(curTac->first->name);
                funcInfo->addCallFunc(curTac->second->name);
            case TAC_ACTUAL:
                {
                    string varName;
                    if(!ifArrParameter(curTac,varName))break;
                    if(varName.c_str()[0] == 'g')
                        modifyGlobalPointerName.insert(varName);
                }
            case TAC_ARR_L:
            case TAC_ZERO:
                if(curTac->first->name[0] == 'g')
                    modifyGlobalPointerName.insert(curTac->first->name);
                break;
            }
        }while(curTac != tacTail);
        delete tacHeadHead;
    }
    for(auto it = arrFormalIndex.begin();it != arrFormalIndex.end();it++)
        it->second = formalNum - 1 - it->second;
    for(uint blockId = 0;blockId < basicBlock.size();blockId++)
    {
        SsaTac* tacHead = basicBlock[blockId]->getTacHead();
        SsaTac* tacTail = basicBlock[blockId]->getTacTail();
        if(tacHead == NULL)continue;      
        SsaTac* tacHeadHead = new SsaTac();
        tacHeadHead->next = tacHead;
        SsaTac* curTac = tacHeadHead; 
        uint actualNum = 0;
        vector<pair<string,uint>> arrIndex;
        arrIndex.clear();
        do
        {
            curTac = curTac->next;
            string varName;
            if(curTac->type != TAC_ACTUAL)continue;
            if(!ifArrParameter(curTac,varName)){actualNum++;continue;}
            arrIndex.push_back(make_pair(varName,actualNum));
            actualNum++;
        }while(curTac != tacTail);
        delete tacHeadHead;
        if(arrIndex.size() == 0)continue;
        string funcName = lookForFuncName(basicBlock[forwardGraph[blockId][0]]);
        for(uint i = 0;i < arrIndex.size();i++)
        {
            arrIndex[i].second = actualNum - 1 - arrIndex[i].second;
            string varName = arrIndex[i].first;
            uint index = arrIndex[i].second;
            if(varName.c_str()[0] == 'g')
                funcInfo->addCallFuncOfGlobalArr(funcName,varName,index);
            else if(arrFormalIndex.find(varName) != arrFormalIndex.end())
                funcInfo->addCallFuncOfLocalArr(funcName,arrFormalIndex[varName],index);
        }
    }
    cout << endl;
}

string FuncPropertyGetter::lookForFuncName(BasicBlock* basicBlock)
{
    SsaTac* tacHead = basicBlock->getTacHead();
    SsaTac* tacTail = basicBlock->getTacTail();
    if(tacHead == NULL)exit(-1);
    SsaTac* tacHeadHead = new SsaTac();
    tacHeadHead->next = tacHead;
    SsaTac* curTac = tacHeadHead; 
    do
    {
        curTac = curTac->next;
        if(curTac->type != TAC_CALL)continue;
        delete tacHeadHead;
        return curTac->second->name;
    }while(curTac != tacTail);
}

bool FuncPropertyGetter::ifArrParameter(SsaTac* codeTac,string& varName)
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
    return false;
}

void FuncPropertyGetter::buildCallGraph(void)
{
    m_backwardGraph.resize(m_funcNameSet.size());
    for(uint i = 0;i < m_backwardGraph.size();i++)
        m_backwardGraph[i].clear();
    for(auto it = m_funcInfoContainers.begin();it != 
                    m_funcInfoContainers.end();it++)
    {
        uint funcNameIndex = m_funcName2index[it->first];
        FuncInfoContainer* container = it->second;
        unordered_set<string>& callFuncList = container->getCallFuncList();
        for(auto iter = callFuncList.begin();iter != callFuncList.end();iter++)
        {
            if(m_funcNameSet.find(*iter) == m_funcNameSet.end())continue;
            uint connectFuncNameIndex = m_funcName2index[*iter];
            m_backwardGraph[connectFuncNameIndex].push_back(funcNameIndex);
        }
    }
}

void FuncPropertyGetter::lowWorksheetAlgorithm(void)
{
    unordered_set<uint> nodeWorkList;
    nodeWorkList.clear();
    for(auto it = m_index2funcName.begin();it != m_index2funcName.end();it++)
        nodeWorkList.insert(it->first);

    while(!nodeWorkList.empty())
    {
        uint curNode = *(nodeWorkList.begin());
        nodeWorkList.erase(curNode);
        
        string curFuncName = m_index2funcName[curNode];
        unordered_set<string>& curGlobalVar = 
        m_funcInfoContainers[curFuncName]->getModifyGlobalName();
        set<string> curGlobalVarTemp;
        curGlobalVarTemp.clear();
        for(auto it = curGlobalVar.begin();it != curGlobalVar.end();it++)
            curGlobalVarTemp.insert(*it);
        for(uint i = 0;i < m_backwardGraph[curNode].size();i++)
        {
            uint callingNode = m_backwardGraph[curNode][i];
            string callingFuncName = m_index2funcName[callingNode];
            unordered_set<string>& callingGlobalVar = 
            m_funcInfoContainers[callingFuncName]->getModifyGlobalName(); 
            uint formerSize = callingGlobalVar.size();
            
            set<string> callingGlobalVarTemp;
            set<string> callingGlobalVarResult;
            callingGlobalVarResult.clear();
            callingGlobalVarTemp.clear();
            for(auto it = callingGlobalVar.begin();it != callingGlobalVar.end();it++)
                callingGlobalVarTemp.insert(*it);
            set_union(curGlobalVarTemp.begin(),curGlobalVarTemp.end(),
            callingGlobalVarTemp.begin(),callingGlobalVarTemp.end(),
            inserter(callingGlobalVarResult,callingGlobalVarResult.begin()));
            for(auto it = callingGlobalVarResult.begin();it != callingGlobalVarResult.end();it++)
                callingGlobalVar.insert(*it);  
            uint laterSize = callingGlobalVar.size();
            if(laterSize != formerSize)nodeWorkList.insert(callingNode);
        }
    }
}


void FuncPropertyGetter::highWorksheetAlgorithm(void)
{
    for(auto it = m_funcInfoContainers.begin();
    it != m_funcInfoContainers.end();it++)
    {
        FuncInfoContainer *container = it->second;
        unordered_map<string,vector<pair<uint,uint>>>& 
            funcFormal2formaled = container->getFuncFormal2formaled();
        unordered_map<string,vector<pair<string,uint>>>& 
            funcGlobal2formaled = container->getFuncGlobal2formaled();
        for(auto iter = funcFormal2formaled.begin();
        iter != funcFormal2formaled.end();iter++)
        {
            string funcName = iter->first;
            if(m_funcNameSet.find(funcName) != m_funcNameSet.end())continue;
            funcFormal2formaled.erase(funcName);
        }
        for(auto iter = funcGlobal2formaled.begin();
        iter != funcGlobal2formaled.end();iter++)
        {
            string funcName = iter->first;
            if(m_funcNameSet.find(funcName) != m_funcNameSet.end())continue;
            funcGlobal2formaled.erase(funcName);
        }
    }
   
    unordered_map<string,unordered_map<string,vector<pair<uint,uint>>>> funcCalled;
    for(auto it = m_funcInfoContainers.begin();
    it != m_funcInfoContainers.end();it++)
    {
        string funcName = it->first;
        FuncInfoContainer *container = it->second;
        unordered_map<string,vector<pair<uint,uint>>>& 
            funcFormal2formaled = container->getFuncFormal2formaled();
        for(auto iter = funcFormal2formaled.begin();
        iter != funcFormal2formaled.end();iter++)
        {
            string callFuncName = iter->first;
            auto iterCall = funcCalled.find(callFuncName);
        }                
    }    
    
   
unordered_set<string> FuncPropertyGetter::getDirtyArrName(void)
{
    unordered_set<string> result;
    result.clear();
    for(auto it = m_funcInfoContainers.begin();
    it != m_funcInfoContainers.end();it++)
    {
        FuncInfoContainer* container = it->second;
        unordered_set<string>& dirtyArrName = container->getModifyGlobalPointerName();
        for(auto iter = dirtyArrName.begin();
        iter != dirtyArrName.end();iter++)
            result.insert(*iter);
    }
    return result;
}
#endif
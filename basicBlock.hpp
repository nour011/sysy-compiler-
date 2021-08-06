//======================================================================
//
//        Copyright (C) 2021 张锦伦    
//        All rights reserved
//
//        filename :basicBlock.hpp
//        description :
//
//        created by 张锦伦 at  03/07/2021 16:02:31
//        
//
//======================================================================

#ifndef BASICBLOCK_HPP
#define BASICBLOCK_HPP
#include "frontEndInput.hpp"
#include "ssaCodeStruct.hpp"
#include <iostream>
#include <vector>
using namespace std;
typedef unsigned int uint;
class BasicBlock
{
private:
public:
    uint m_id;                                              
    uint m_instNum;                                         
    SsaTac* m_tacHead;                                      
    SsaTac* m_tacTail;                                      
private:
    void cleanDirtyTac(bool isNeedDelete);                  
    void placeInsertTac(SsaTac* newTac);                    
public:
    BasicBlock();
    ~BasicBlock();
    void printBasicBlock(void);                                       
    void cleanDirtyTac(void);                              
    void raiseUnUseTac(void);                               
    void setId(uint id);                                    
    void setinstNum(uint instNum){m_instNum=instNum;}       
    void setTacHead(SsaTac* tacHead){m_tacHead=tacHead;}    
    void setTacTail(SsaTac* tacTail){m_tacTail=tacTail;}    
    void insertPsiFunction(SsaSymb* temp,uint size);        
    SsaTac* getTacTail(void){return m_tacTail;};            
    SsaTac* getTacHead(void){return m_tacHead;};            
    uint getInstNum(void){return m_instNum;};               
    void insertTacToTail(SsaTac* newTac);                  
};

BasicBlock::BasicBlock()
{
    m_instNum = 0;
    m_tacHead = m_tacTail = NULL;
}

BasicBlock::~BasicBlock()
{

}
void BasicBlock::setId(uint id)
{
    m_id=id;
    if(m_tacHead == NULL)return;
    SsaTac* tacHeadHead = new SsaTac();
    tacHeadHead->next = m_tacHead;
    SsaTac* curTac = tacHeadHead;
    do
    {
        curTac = curTac->next;
        curTac->blockId = id;
    } while (curTac != m_tacTail);
    delete tacHeadHead;
        
}

void BasicBlock::printBasicBlock(void)
{
    cout << endl << "blockId: B" <<  m_id << endl;
    if(m_tacHead == NULL)return;
    SsaTac* tacHeadHead = new SsaTac();
    tacHeadHead->next = m_tacHead;
    SsaTac* curTac = tacHeadHead;
    do
    {
        curTac = curTac->next;
        printOneSsaTac(curTac);
        printf("\n");
    } while (curTac != m_tacTail);
    delete tacHeadHead;
}

void BasicBlock::insertPsiFunction(SsaSymb* temp,uint size)
{
    SsaTac* addNode = new SsaTac();
    addNode->type = TAC_INSERT;
    addNode->blockId = m_id;
    addNode->first = createSsaSymbFromSsaSymb(temp);
    addNode->functionSymb.resize(size);
    for(uint i = 0;i < size;i++)
        addNode->functionSymb[i] = 
        createSsaSymbFromSsaSymb(temp);

    addNode->functionSymb2Tac.resize(size);
    if(m_tacHead == NULL)
        m_tacHead = m_tacTail = addNode;
    else 
    {
        addNode->next = m_tacHead;
        m_tacHead->prev = addNode;
        m_tacHead = addNode;
    }
    m_instNum++;
}

void BasicBlock::cleanDirtyTac(void)
{
    cleanDirtyTac(true);
} 

void BasicBlock::cleanDirtyTac(bool isNeedDelete)
{
    if(m_tacHead == NULL)return;
    vector<SsaTac*> needToSaveList;
    vector<SsaTac*> needToDeleteList;
    needToSaveList.clear();
    needToDeleteList.clear();

    SsaTac* tacHeadHead = new SsaTac();
    tacHeadHead->next = m_tacHead;
    SsaTac* curTac = tacHeadHead;
    do
    {
        curTac = curTac->next;
        if(curTac->type == TAC_UNDEF)
            needToDeleteList.push_back(curTac);
        else needToSaveList.push_back(curTac);
    } while (curTac!=m_tacTail);
    delete tacHeadHead;
    m_instNum = m_instNum - needToDeleteList.size();
    if(isNeedDelete == true)
    {
        for(uint i = 0;i < needToDeleteList.size();i++)
            delete needToDeleteList[i];
    }

    if(needToSaveList.size() == 0)
    {
        m_tacHead = m_tacTail = NULL;
        return;
    }
    m_tacHead = needToSaveList[0];
    m_tacTail = needToSaveList[0];
    for(uint i = 1;i < needToSaveList.size();i++)
    {
        m_tacTail->next = needToSaveList[i];
        needToSaveList[i]->prev = m_tacTail;
        m_tacTail = needToSaveList[i];
    }    
}

void BasicBlock::raiseUnUseTac(void)
{
    cleanDirtyTac(false);
}

void BasicBlock::insertTacToTail(SsaTac* newTac)
{
    m_instNum++;
    newTac->prev = NULL;
    newTac->next = NULL;
    if(newTac->type == TAC_INSERT)
    {
        placeInsertTac(newTac);
        return;
    }
    if(m_tacHead == NULL)
    {
        m_tacHead = m_tacTail = newTac;
        return;
    }
 
    if(m_tacTail->type != TAC_GOTO)
    {
        m_tacTail->next = newTac;
        newTac->prev = m_tacTail;
        m_tacTail = newTac;
        return;
    }
    if(m_tacTail == m_tacHead)
    {
        m_tacHead = newTac;
        m_tacHead->next = m_tacTail;
        m_tacTail->prev = m_tacHead;
        return;
    }
    m_tacTail->prev->next = newTac;
    newTac->prev = m_tacTail->prev;
    m_tacTail->prev = newTac;
    newTac->next = m_tacTail;
}

void BasicBlock::placeInsertTac(SsaTac* newTac)
{
    if(m_tacHead == NULL)
    {
        m_tacHead = newTac;
        m_tacTail = newTac;
        return;
    }
    if(m_tacTail->type == TAC_INSERT)
    {
        m_tacTail->next = newTac;
        newTac->prev = m_tacTail;
        m_tacTail = newTac;
        return;
    }
    SsaTac* tacTailTail = new SsaTac();
    tacTailTail->prev = m_tacTail;
    SsaTac* curTac = tacTailTail;  
    do
    {
        curTac = curTac->prev;
        if(curTac->type != TAC_INSERT)continue;
        newTac->prev = curTac;
        newTac->next = curTac->next;
        curTac->next->prev = newTac;
        curTac->next = newTac;
        return;
    } while (curTac != m_tacHead);
    delete tacTailTail;

    m_tacHead->prev = newTac;
    newTac->next = m_tacHead;
    m_tacHead = newTac;
}

#endif
#ifndef GLOBALPOLICYEXECUTOR_HPP
#define GLOBALPOLICYEXECUTOR_HPP
#include "functionBlock.hpp"
#include "funcPropertyGetter.hpp"

class GlobalPolicyExecutor
{
protected:
    FunctionBlock* m_block;
    string m_name;
public:
    GlobalPolicyExecutor();
    ~GlobalPolicyExecutor();

    virtual void printInfoOfOptimizer(void) = 0;        
    virtual bool runOptimizer(FunctionBlock* block,
        FuncPropertyGetter* funcPropertyGetter) = 0;
    string getOptimizerName(void){return m_name;};
};

GlobalPolicyExecutor::GlobalPolicyExecutor()
{

}

GlobalPolicyExecutor::~GlobalPolicyExecutor()
{
    
}


#endif
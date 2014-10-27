#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

/* symbol tables for semantic checking. */
SymbolTable<Symbol, Feature> *function_table;
SymbolTable<Symbol, Symbol> *attribute_table;

ClassTable *classtable;

/* TO DO - not return after semant_error() */
ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    /* Fill this in */
    install_basic_classes();
    
    int is_Main_present = 0;
    int is_error = 0;
    std::map<Symbol, Class_>::iterator it;
    for(int i=classes->first(); classes->more(i); i=classes->next(i))
    {

        Class_ current_class = classes->nth(i);

        Symbol current_class_name = current_class->get_name();
        Symbol current_class_parent = current_class->get_parent();

        /* checking if the class is not currently present. */
        it = inheritance_graph.find(current_class_name);
        if(it!=inheritance_graph.end())
        {
            semant_error(current_class)<<"Class "<<current_class_name<<" was previously defined.\n";
        }

        /* checking if the class doesnt inherit itself. */
        if(current_class_name==current_class_parent)
        {
            semant_error(current_class)<<"Class "<<current_class_name<<", or an ancestor of "<<current_class_name<<", is involved in an inheritance cycle"<<endl;
        }

        else if(current_class_name==SELF_TYPE)
        {
            semant_error(current_class)<<"Redifination of basic class SELF_TYPE\n";   
        }

        /* checking if the class doesn't inherit the basic types. */
        else if(current_class_parent==Bool || current_class_parent==Int || current_class_parent==Str || current_class_parent==SELF_TYPE)
        {
            semant_error(current_class)<<"Class "<<current_class_name<<" cannot inherit class "<<current_class_parent<<".\n";
        }

        /* inserting the current class in the map. */
        else{
            inheritance_graph.insert(std::pair<Symbol, Class_>(current_class_name, current_class));
        }
        
        /* checking if Main exists. */
        if(current_class_name==Main)
            is_Main_present = 1;
    }

    /* if Main not found. */
    if(is_Main_present==0)
    {
        semant_error()<<"Class Main is not defined.\n";
    }

    /* checking for cycle in the graph. */
    for(it = inheritance_graph.begin(); it!=inheritance_graph.end(); it++)
    {
        /* checking for cycle from this class as the first class. */
        bool is_cycle = false;
        
        Symbol slow_iterator, fast_iterator;
        slow_iterator = fast_iterator = it->first;

        if(slow_iterator==Object)
            continue;

        while(1)
        {
            if(inheritance_graph.find(inheritance_graph.find(slow_iterator)->second->get_parent())==inheritance_graph.end())
            {
                semant_error(inheritance_graph.find(slow_iterator)->second)<<"Class "<<slow_iterator<<" inherits from an undefined class "<<inheritance_graph.find(slow_iterator)->second->get_parent()<<".\n";
                return;
            }
            slow_iterator = inheritance_graph.find(slow_iterator)->second->get_parent();
            
            if(inheritance_graph.find(inheritance_graph.find(fast_iterator)->second->get_parent())==inheritance_graph.end())
            {
                semant_error(inheritance_graph.find(fast_iterator)->second)<<"Class "<<fast_iterator<<" inherits from an undefined class "<<inheritance_graph.find(fast_iterator)->second->get_parent()<<".\n";
                return;
            }
            fast_iterator = inheritance_graph.find(fast_iterator)->second->get_parent();
            if(fast_iterator!=Object)
            {
                if(inheritance_graph.find(inheritance_graph.find(fast_iterator)->second->get_parent())==inheritance_graph.end())
                {
                    semant_error(inheritance_graph.find(fast_iterator)->second)<<"Class "<<fast_iterator<<" inherits from an undefined class "<<inheritance_graph.find(fast_iterator)->second->get_parent()<<".\n";
                    return;
                }
                fast_iterator = inheritance_graph.find(fast_iterator)->second->get_parent();
            }

            if(slow_iterator==Object || fast_iterator==Object)
                break;

            if(slow_iterator==fast_iterator)
            {
                is_cycle = true;
                break;
            }
        }

        if(is_cycle)
        {
            semant_error(it->second)<<"Class "<<it->first<<", or an ancestor of "<<it->first<<", is involved in an inheritance cycle"<<endl;
        }
    }

}
void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
    class_(Object, 
           No_class,
           append_Features(
                   append_Features(
                           single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
                           single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
                   single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
           filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
    class_(IO, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   single_Features(method(out_string, single_Formals(formal(arg, Str)),
                                              SELF_TYPE, no_expr())),
                                   single_Features(method(out_int, single_Formals(formal(arg, Int)),
                                              SELF_TYPE, no_expr()))),
                           single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
                   single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
           filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
    class_(Int, 
           Object,
           single_Features(attr(val, prim_slot, no_expr())),
           filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
    class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
    class_(Str, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   append_Features(
                                           single_Features(attr(val, Int, no_expr())),
                                           single_Features(attr(str_field, prim_slot, no_expr()))),
                                   single_Features(method(length, nil_Formals(), Int, no_expr()))),
                           single_Features(method(concat, 
                                      single_Formals(formal(arg, Str)),
                                      Str, 
                                      no_expr()))),
                   single_Features(method(substr, 
                              append_Formals(single_Formals(formal(arg, Int)), 
                                     single_Formals(formal(arg2, Int))),
                              Str, 
                              no_expr()))),
           filename);

    inheritance_graph.insert(std::pair<Symbol, Class_>(Object, Object_class));
    inheritance_graph.insert(std::pair<Symbol, Class_>(IO, IO_class));
    inheritance_graph.insert(std::pair<Symbol, Class_>(Int, Int_class));
    inheritance_graph.insert(std::pair<Symbol, Class_>(Bool, Bool_class));
    inheritance_graph.insert(std::pair<Symbol, Class_>(Str, Str_class));
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

bool subClass(Symbol first, Symbol parent)
{
    while(first!=No_class)
    {
        first = inheritance_graph.find(first)->second->get_parent();
        if(first == parent)
            return true;
    }
    return false;
}

Feature getmethods(Class_ cur_class , Symbol method_name)
{
    Feature feature = NULL;
    Symbol feature_name;
    Features features = cur_class->get_features();
    for(int i=features->first();features->more(i);i=features->next(i))
    {
        feature = features->nth(i);
        feature_name = feature->get_name();
        if(feature_name==method_name)
            return feature;
    }
    Symbol parent = cur_class->get_parent();
    if(inheritance_graph.find(parent)==inheritance_graph.end())
        return NULL;
    cur_class = inheritance_graph.find(parent)->second;
    return getmethods(cur_class,method_name);
}

Symbol assign_class::get_expression_type(Class_ cur_class)
{
    Symbol *left_type = attribute_table->lookup(name);
    if(left_type==NULL)
    {
        classtable->semant_error(cur_class)<<"Assignment to undeclared variable "<<name<<".\n";
        type = Object;
        return Object;
    }

    Symbol right_type = expr->get_expression_type(cur_class);
    if(*left_type!=right_type && (!subClass(right_type,*left_type)))
    {
        classtable->semant_error(cur_class)<<"Type "<<right_type<<" of assigned expression does not conform to declared type "<<*left_type<<" of identifier "<<name<<".\n";
        type = Object;
        return Object;
    }

    type = *left_type;
    return *left_type;
}

Symbol static_dispatch_class::get_expression_type(Class_ cur_class)
{
    Symbol first_expr_type = expr->get_expression_type(cur_class);
    if(inheritance_graph.find(type_name)==inheritance_graph.end())
    {
        classtable->semant_error(cur_class)<<"Class "<<type_name<<" is undefined\n";
        type = Object;
        return type;
    }
    if(first_expr_type==SELF_TYPE)
        first_expr_type=cur_class->get_name();
    if(first_expr_type!=type_name &&(!subClass(first_expr_type,type_name)))
    {
        classtable->semant_error(cur_class)<<"Expression type "<<first_expr_type<<" is not of inherited from class"<<type_name<<endl;
        type = Object;
        return type;
    }

    Feature feature = getmethods(inheritance_graph.find(type_name)->second,name);
    if(feature==NULL)
    {
        classtable->semant_error(cur_class)<<"Method "<<name<<" is undefined\n";
        type = Object;
        return type;
    }

    Formals def_formals = feature->get_formals();
    int num_actuals = actual->len();
    int num_formals = def_formals->len();
    if(num_actuals!=num_formals)
    {
        classtable->semant_error(cur_class)<<"Lenght of Actuals is not equal to the formals\n";
        type = Object;
        return type;
    }
    for(int i=actual->first();actual->more(i);i=actual->next(i))
    {
        Symbol actual_type = actual->nth(i)->get_expression_type(cur_class);
        Symbol formal_type = def_formals->nth(i)->get_type();
        if(actual_type!=formal_type&& (!subClass(actual_type,formal_type)))
        {
            classtable->semant_error(cur_class)<<"Actuals does not conforms with the Formals\n";
            type = Object;
            return type;
        }
    }

    type = feature->get_return_type();
    if(type==SELF_TYPE)
        type = first_expr_type;
    return type;
}

Symbol dispatch_class::get_expression_type(Class_ cur_class)
{
    Symbol first_expr_type = expr->get_expression_type(cur_class);
    if(inheritance_graph.find(first_expr_type)==inheritance_graph.end())
    {
        classtable->semant_error(cur_class)<<"Class "<<first_expr_type<<" is undefined.\n";
        type = Object;
        return type;
    }
    Feature feature;
    if(first_expr_type==SELF_TYPE)
        feature = getmethods(cur_class,name);
    else 
        feature = getmethods(inheritance_graph.find(first_expr_type)->second,name);
    if(feature==NULL)
    {
        classtable->semant_error(cur_class)<<"Method "<<name<<" is undefined.\n";
        type = Object;
        return type;   
    }
    Formals def_formals = feature->get_formals();
    int num_actuals = actual->len();
    int num_formals = def_formals->len();
    if(num_actuals!=num_formals)
    {
        classtable->semant_error(cur_class)<<"Lenght of Actuals is not equal to the formals\n";
        type = Object;
        return type;
    }
    for(int i=actual->first();actual->more(i);i=actual->next(i))
    {
        Symbol actual_type = actual->nth(i)->get_expression_type(cur_class);
        Symbol formal_type = def_formals->nth(i)->get_type();
        if(actual_type==SELF_TYPE)
            actual_type=cur_class->get_name();
        if(actual_type!=formal_type&& (!subClass(actual_type,formal_type)))
        {
            classtable->semant_error(cur_class)<<"Actuals does not conforms with the Formals\n";
            type = Object;
            return type;
        }
    }
    type = feature->get_return_type();
    if(type ==SELF_TYPE)
        type = first_expr_type;
    return type;
}

Symbol cond_class::get_expression_type(Class_ cur_class)
{
    return No_type;
}

Symbol loop_class::get_expression_type(Class_ cur_class)
{
    if(pred->get_expression_type(cur_class)!=Bool)
    {
        classtable->semant_error(cur_class)<<"Loop condition does not have type Bool.\n";
    }
    body->get_expression_type(cur_class);
    type = Object;
    return Object;
}

Symbol typcase_class::get_expression_type(Class_ cur_class)
{
    return No_type;
}

Symbol block_class::get_expression_type(Class_ cur_class)
{
    Symbol expr_type;
    for(int i=body->first();body->more(i);i=body->next(i))
    {
        expr_type=body->nth(i)->get_expression_type(cur_class);
    }
    type = expr_type;
    return expr_type;
}

Symbol let_class::get_expression_type(Class_ cur_class)
{
    return No_type;
}

Symbol plus_class::get_expression_type(Class_ cur_class)
{
    if(e1->get_expression_type(cur_class)!=Int || e2->get_expression_type(cur_class)!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<e1->get_expression_type(cur_class)<<" + "<<e2->get_expression_type(cur_class)<<".\n";
        type = Object;
        return Object;
    }
    type = Int;
    return Int;
}

Symbol sub_class::get_expression_type(Class_ cur_class)
{
    if(e1->get_expression_type(cur_class)!=Int || e2->get_expression_type(cur_class)!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<e1->get_expression_type(cur_class)<<" - "<<e2->get_expression_type(cur_class)<<".\n";
        type = Object;
        return Object;
    }
    type = Int;
    return Int;
}

Symbol mul_class::get_expression_type(Class_ cur_class)
{
    if(e1->get_expression_type(cur_class)!=Int || e2->get_expression_type(cur_class)!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<e1->get_expression_type(cur_class)<<" * "<<e2->get_expression_type(cur_class)<<".\n";
        type = Object;
        return Object;
    }
    type = Int;
    return Int;
}

Symbol divide_class::get_expression_type(Class_ cur_class)
{
    if(e1->get_expression_type(cur_class)!=Int || e2->get_expression_type(cur_class)!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<e1->get_expression_type(cur_class)<<" / "<<e2->get_expression_type(cur_class)<<".\n";
        type = Object;
        return Object;
    }
    type = Int;
    return Int;
}

Symbol neg_class::get_expression_type(Class_ cur_class)
{
    Symbol expr_type = e1->get_expression_type(cur_class);
    if(expr_type!=Int)
    {
        classtable->semant_error(cur_class)<<"Argument of '~' has type "<<expr_type<<" instead of Int.\n";
        type = Object;
        return Object;
    }
    type = Int;
    return Int;
}

Symbol lt_class::get_expression_type(Class_ cur_class)
{
    Symbol left = e1->get_expression_type(cur_class);
    Symbol right = e2->get_expression_type(cur_class);
    if(left!=Int || right!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<left<<" < "<<right<<"\n";
        type = Object;
        return Object;
    }
    type = Bool;
    return Bool;
}

Symbol eq_class::get_expression_type(Class_ cur_class)
{
    Symbol left = e1->get_expression_type(cur_class);
    Symbol right = e2->get_expression_type(cur_class);
    if(((left==Int|| right==Int) || (left==Bool|| right==Bool) || (left==Str|| right==Str))&& (left!=right))
    {
        classtable->semant_error(cur_class)<<"Invalid comparison between two classes\n";
        type = Object;
        return Object;
    }
    type = Bool;
    return Bool;

}

Symbol leq_class::get_expression_type(Class_ cur_class)
{
    Symbol left = e1->get_expression_type(cur_class);
    Symbol right = e2->get_expression_type(cur_class);
    if(left!=Int || right!=Int)
    {
        classtable->semant_error(cur_class)<<"non-Int arguments: "<<left<<" <= "<<right<<"\n";
        type = Object;
        return Object;
    }
    type = Bool;
    return Bool;
}

Symbol comp_class::get_expression_type(Class_ cur_class)
{
    Symbol expr_type=e1->get_expression_type(cur_class);
    if(expr_type!=Bool)
    {
        classtable->semant_error(cur_class)<<"Argument of 'not' has type "<<expr_type<<".\n";
        type = Object;
        return Object;
    }
    type = Bool;
    return Bool;
}

Symbol int_const_class::get_expression_type(Class_ cur_class)
{
    type = Int;
    return Int;
}

Symbol bool_const_class::get_expression_type(Class_ cur_class)
{
    type = Bool;
    return Bool;
}

Symbol string_const_class::get_expression_type(Class_ cur_class)
{
    type = Str;
    return Str;
}

Symbol new__class::get_expression_type(Class_ cur_class)
{
    if(type_name==SELF_TYPE)
    {   
        type = SELF_TYPE;
        return type;
    }
    if(inheritance_graph.find(type_name)==inheritance_graph.end())
    {
        classtable->semant_error(cur_class)<<"'new' used with undefined class "<<type_name<<endl;
        type = Object;
        return Object;
    }
    type = type_name;
    return type_name;
}

Symbol isvoid_class::get_expression_type(Class_ cur_class)
{
    e1->get_expression_type(cur_class);
    type = Bool;
    return Bool;
}

Symbol no_expr_class::get_expression_type(Class_ cur_class)
{
    type = No_type;
    return No_type;
}

Symbol object_class::get_expression_type(Class_ cur_class)
{
    if(name == self)
    {
        type = SELF_TYPE;
        return type;
    }
    Symbol* obj_type = attribute_table->lookup(name);
    if(obj_type==NULL)
    {
        classtable->semant_error(cur_class)<<"Undefined identifier "<<name<<endl;
        type = Object;
        return Object;
    }
    type = *obj_type;
    return type;
}

void method_class::check_feature(Class_ cur_class)
{
    bool err_flag=false;
    for(int i=formals->first();formals->more(i);i=formals->next(i))
    {
        Formal formal = formals->nth(i);
        Symbol formal_name = formal->get_name();
        if(formal_name == self)
        {
            classtable->semant_error(cur_class)<<"'self' cannot be a formal parameter\n";
            err_flag=true;
        }
        if(inheritance_graph.find(formal->get_type())==inheritance_graph.end())
        {
            classtable->semant_error(cur_class)<<"Class "<<formal->get_type()<<" of formal parameter "<<formal_name<<" is undefined\n";
            err_flag=true;   
        }
        if(attribute_table->probe(formal_name)!=NULL)
        {
            classtable->semant_error(cur_class)<<"Formal parameter "<<formal_name<<" is multiply defined\n";
            err_flag=true;
        }
        if(!err_flag)
        {
            attribute_table->addid(formal_name, new Symbol(formal->get_type()));
        }
    }
    Symbol expr_type=expr->get_expression_type(cur_class);
    Symbol r_type = return_type;
    if(r_type==SELF_TYPE)
        r_type=cur_class->get_name();
    if(expr_type==SELF_TYPE)
        expr_type=cur_class->get_name();
    if(expr_type!=return_type && (!subClass(expr_type,return_type)))
    {
        classtable->semant_error(cur_class)<<"Inferred return type "<<expr_type<<" of method "<<name<<" does not conform to declared type "<<return_type<<".\n";
    }


}

void attr_class::check_feature(Class_ cur_class)
{
    Symbol assigned_type = init->get_expression_type(cur_class);
    if(assigned_type==SELF_TYPE)
        assigned_type=cur_class->get_name();
    Symbol decl_type = type_decl;
    if(decl_type==SELF_TYPE)
        decl_type=cur_class->get_name();
    if(inheritance_graph.find(decl_type)==inheritance_graph.end())
    {
        classtable->semant_error(cur_class)<<"Class "<<type_decl<<" of attribute "<<name<<" is undefined"<<endl;
    }

    if(assigned_type!=No_type && assigned_type!=type_decl && (!subClass(assigned_type,type_decl)))
    {
        classtable->semant_error(cur_class)<<"Inferred type "<<assigned_type<<" of initialization of attribute "<<name<<" does not conform to declared type "<<type_decl<<".\n";
    }
}

void method_class::add_to_symbol_table(Feature current_feature, Class_ cur_class)
{
    bool is_error=false;
    if(function_table->probe(name)!=NULL)
    {
        classtable->semant_error(cur_class)<<"Method "<<name<<" is multiply defined.\n";
        return;
    }

    if(function_table->lookup(name)!= NULL)
    {
        Feature inherited_feature = *(function_table->lookup(name));
        Formals inherited_formals = inherited_feature->get_formals();

        if(formals->len()!=inherited_formals->len())
        {
            classtable->semant_error(cur_class)<<"Incompatible number of formal parameters in redefined method "<<name<<".\n";
            return;  
        }

        for(int i=formals->first(); formals->more(i); i=formals->next(i))
        {
            Formal current_formal = formals->nth(i);
            Formal inherited_formal = inherited_formals->nth(i);

            if(current_formal->get_type()!=inherited_formal->get_type())
            {
                classtable->semant_error(cur_class)<<"In redefined method "<<name<<", parameter type "<<current_formal->get_type()<<" is different from original type "<<inherited_formal->get_type()<<".\n";
                is_error=true;
                break;
            }
        }

        if(return_type!=inherited_feature->get_return_type())
        {
            classtable->semant_error(cur_class)<<"In redefined method "<<name<<", return type "<<return_type<<" is different from original return type "<<inherited_feature->get_return_type()<<".\n";
            return;
        }
    }
    if(!is_error)
        function_table->addid(name, new Feature(current_feature));

}

void attr_class::add_to_symbol_table(Feature current_feature, Class_ cur_class)
{
    if(attribute_table->probe(name)!=NULL)
    {
        classtable->semant_error(cur_class)<<"Attribute "<<name<<" is multiply defined in class.\n";
        return;
    }

    if(attribute_table->lookup(name)!=NULL)
    {
        classtable->semant_error(cur_class)<<"Attribute "<<name<<" is an attribute of an inherited class.\n";
        return;
    }

    if(name==self)
    {
        classtable->semant_error(cur_class)<<"'self' cannot be the name of an attribute.\n";
        return;
    }
    if(type_decl==SELF_TYPE){
        attribute_table->addid(name, new Symbol(cur_class->get_name()));
        return;
    }    
    attribute_table->addid(name, new Symbol(type_decl));
}

void populate_symbol_tables(Class_ cur_class)
{
    Symbol parent = cur_class->get_parent();
    if(parent!=No_class)
    {
        populate_symbol_tables(inheritance_graph.find(parent)->second);
    }

    attribute_table->enterscope();
    function_table->enterscope();

    Features features = cur_class->get_features();

    for(int i=features->first(); features->more(i); i=features->next(i))
    {
        Feature feature = features->nth(i);
        feature->add_to_symbol_table(features->nth(i), cur_class);
    }
}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    classtable = new ClassTable(classes);
    if (classtable->errors()) {
    cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
    }
    /* some semantic analysis code may go here */
    for(int i=classes->first(); classes->more(i); i=classes->next(i))
    {
        /* getting the current class. */
        Class_ cur_class = classes->nth(i);
        function_table = new SymbolTable<Symbol, Feature>();
        attribute_table = new SymbolTable<Symbol, Symbol>();
        populate_symbol_tables(cur_class);

        Features features = cur_class->get_features();
        for(int i=features->first(); features->more(i); i=features->next(i))
        {
            Feature feature = features->nth(i);

            attribute_table->enterscope();
            function_table->enterscope();

            feature->check_feature(cur_class);

            attribute_table->exitscope();
            function_table->exitscope();

        }
    }

    if (classtable->errors()) {
    cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
    }
}

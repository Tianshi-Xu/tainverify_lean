import os
import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any
import time
from openai import AzureOpenAI
from azure.identity import DefaultAzureCredential, get_bearer_token_provider

# 配置
endpoint = os.getenv("ENDPOINT_URL", "https://ai4mtest1.openai.azure.com/")
deployment = os.getenv("DEPLOYMENT_NAME", "gpt-5")

# Initialize Azure OpenAI client with Entra ID authentication
credential = DefaultAzureCredential(managed_identity_client_id="7e0d39de-9cb1-4585-85af-1e82ea00b36d")
token_provider = get_bearer_token_provider(credential, "https://cognitiveservices.azure.com/.default")

client = AzureOpenAI(
    azure_endpoint=endpoint,
    azure_ad_token_provider=token_provider,
    api_version="2025-01-01-preview",
)

def create_prompt(operator: Dict[str, Any], simd_lean: str) -> str:
    """
    创建请求的prompt模板
    你可以根据需要修改这个模板
    """
    name = operator.get("name", "Unknown")
    url = operator.get("url", "")
    details = operator.get("details", {})

    prompt = f"""下面我分别给你"lean4语言撰写的SIMD算子形式化定义"，以及"一个ONNX算子的自然语言定义"，请分析该ONNX算子是否可以转成SIMD算子，如果可以，请给出足够细粒度的自然语言描述，包括核函数和映射函数，每一步都必须是直接的简单的推导，不能存在复杂的跳步，并且所有符号都要求有明确的定义。如果你认为不行，例如该算子是attention这样的过于复杂的运算，或者其他原因，请回复:"该算子无法转换为SIMD算子"。
    下面是lean4语言撰写的SIMD算子形式化定义:
    {simd_lean}
    下面是ONNX算子的自然语言定义:
    - 名称: {name}
    - 具体描述: {details}
    """

    return prompt

def process_single_operator(operator: Dict[str, Any], simd_lean: str, max_retries: int = 3) -> Dict[str, Any]:
    """
    处理单个算子的请求
    """
    for attempt in range(max_retries):
        try:
            prompt = create_prompt(operator, simd_lean)

            messages = [
                {
                    "role": "system",
                    "content": "你是一个专业的机器学习和深度学习专家，熟悉其中的算子。",
                },
                {
                    "role": "user",
                    "content": prompt,
                }
            ]

            completion = client.chat.completions.create(
                model=deployment,
                messages=messages,
                max_completion_tokens=8192,
                stop=None,
                stream=False
            )
            print(completion)
            result = {
                "operator_name": operator.get("name", "Unknown"),
                "operator_url": operator.get("url", ""),
                "prompt": prompt,
                "response": completion.choices[0].message.content,
                "success": True,
                "attempt": attempt + 1,
                "timestamp": time.time()
            }

            print(f"✅ 成功处理算子: {operator.get('name', 'Unknown')}")
            return result

        except Exception as e:
            print(f"❌ 处理算子 {operator.get('name', 'Unknown')} 时出错 (尝试 {attempt + 1}/{max_retries}): {str(e)}")

            if attempt == max_retries - 1:  # 最后一次尝试失败
                return {
                    "operator_name": operator.get("name", "Unknown"),
                    "operator_url": operator.get("url", ""),
                    "prompt": create_prompt(operator),
                    "response": None,
                    "success": False,
                    "error": str(e),
                    "attempt": attempt + 1,
                    "timestamp": time.time()
                }

            # 重试前等待
            time.sleep(2 ** attempt)  # 指数退避

def process_operators_parallel(operators: List[Dict[str, Any]], simd_lean: str, max_workers: int = 5) -> List[Dict[str, Any]]:
    """
    并行处理所有算子（使用ThreadPoolExecutor）
    """
    print(f"开始处理 {len(operators)} 个ONNX算子，最大并发数: {max_workers}")

    start_time = time.time()
    results = []

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # 提交所有任务
        future_to_operator = {
            executor.submit(process_single_operator, op, simd_lean): op
            for op in operators
        }

        # 收集结果
        for future in as_completed(future_to_operator):
            try:
                result = future.result()
                results.append(result)
            except Exception as e:
                operator = future_to_operator[future]
                results.append({
                    "operator_name": operator.get("name", "Unknown"),
                    "operator_url": operator.get("url", ""),
                    "prompt": create_prompt(operator,simd_lean),
                    "response": None,
                    "success": False,
                    "error": str(e),
                    "attempt": 0,
                    "timestamp": time.time()
                })

    end_time = time.time()

    # 统计结果
    successful = sum(1 for r in results if r["success"])
    failed = len(results) - successful

    print(f"\n处理完成!")
    print(f"总耗时: {end_time - start_time:.2f} 秒")
    print(f"成功: {successful} 个")
    print(f"失败: {failed} 个")

    return results

def load_operators(file_path: str) -> List[Dict[str, Any]]:
    """加载ONNX算子数据"""
    with open(file_path, 'r', encoding='utf-8') as f:
        return json.load(f)

def read_file(file_path: str) -> str:
    """读取文件内容"""
    with open(file_path, 'r', encoding='utf-8') as f:
        return f.read()

def save_results(results: List[Dict[str, Any]], output_file: str):
    """保存结果到文件"""
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(results, f, ensure_ascii=False, indent=2)
    print(f"结果已保存到: {output_file}")

def operators_filter(operators):
    with open("trainverify/onnx_types.json", 'r', encoding='utf-8') as f:
        op_types = json.load(f)
    accepted_ops = [item["name"] for item in op_types[0]["operators"] if item["difficulty"]=="简单"]
    print(accepted_ops)
    """过滤算子"""
    filtered = []
    for op in operators:
        name = op.get("name", "")
        if name not in accepted_ops:
            continue
        filtered.append(op)
    return filtered

def main():
    """主函数"""
    # 加载SIMD定义
    simd_lean = read_file("trainverify/SIMDDefinition.lean")
    # 加载算子数据
    operators = load_operators("trainverify/onnx_operators.json")
    operators = operators_filter(operators)
    print(f"过滤后剩 {len(operators)} 个算子。")
    # 可以只处理前几个算子进行测试
    # operators = operators[34:35]  # 取消注释来测试前5个算子
    # print(operators[0].get("name"))
    # 处理所有算子
    results = process_operators_parallel(operators, simd_lean, max_workers=5)

    # 保存结果
    output_file = f"trainverify/onnx_operators_analysis.json"
    save_results(results, output_file)

    # 打印一些统计信息
    successful_results = [r for r in results if r["success"]]
    if successful_results:
        print(f"\n示例成功结果 (算子: {successful_results[0]['operator_name']}):")
        print("=" * 50)
        print(successful_results[0]['response'][:200] + "..." if len(successful_results[0]['response']) > 200 else successful_results[0]['response'])

if __name__ == "__main__":
    main()

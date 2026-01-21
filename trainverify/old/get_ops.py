import requests
from bs4 import BeautifulSoup
import pandas as pd
from urllib.parse import urljoin
import time

def get_operator_links(index_url):
    """
    从主页面获取所有 Operator 的详情页链接。
    (新版本：增加了对链接文本的检查，以排除指向旧版本的数字链接)
    """
    try:
        response = requests.get(index_url, timeout=10)
        response.raise_for_status()
        soup = BeautifulSoup(response.content, 'html.parser')

        links = []
        # 筛选条件1: 找到所有 class="reference internal" 的 <a> 标签
        for a_tag in soup.find_all('a', class_='reference internal'):
            href = a_tag.get('href', '')

            # 筛选条件2: 链接地址（href）必须以 "op_" 开头，这是主列表页的特征
            if href.startswith('op_') or href.startswith('onnx__'):
                # 在 <a> 标签内找到 <span> 标签
                span_tag = a_tag.find('span')

                # 筛选条件3: 确保 <span> 标签存在，并且其内容不是纯数字
                if span_tag and not span_tag.text.strip().isdigit():
                    # 这是一个有效的主算子链接，将其转换为完整 URL
                    full_url = urljoin(index_url, href)
                    links.append(full_url)

        # 使用 set 去除可能存在的重复链接，然后排序返回
        return sorted(list(set(links)))

    except requests.exceptions.RequestException as e:
        print(f"Error fetching index page {index_url}: {e}")
        return []

def scrape_operator_details(operator_url):
    """
    (最终健壮版 V3)
    从单个 Operator 详情页抓取详细信息。
    - 以 <section> 标签为核心进行迭代。
    - 使用 section['id'] 作为标题。
    - 提取 H3 之后的所有同级元素内容，防止信息截断。
    """
    try:
        print(f"Scraping: {operator_url}")
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        }
        response = requests.get(operator_url, headers=headers, timeout=10)
        response.raise_for_status()
        soup = BeautifulSoup(response.content, 'html.parser')

        op_name = soup.find('h1').text.strip().replace('¶', '') if soup.find('h1') else 'N/A'

        latest_version_section = None
        first_h2 = soup.find('h2')
        if first_h2:
            latest_version_section = first_h2.find_parent('section')

        if not latest_version_section:
            print(f"  [Warning] Could not find a versioned section in {operator_url}.")
            return {'name': op_name, 'url': operator_url, 'details': {}}

        details = {}

        # --- 全新核心逻辑 ---
        # 1. 在最新版本区块内，直接查找所有作为小节的 <section> 标签
        #    这些小节通常都有一个 h3 标题
        sub_sections = latest_version_section.find_all('section', recursive=False)

        for section in sub_sections:
            # 2. 使用 section 的 'id' 作为标题，这是最可靠的方式
            if not section.has_attr('id'):
                continue

            # 将 id (如 "type-constraints") 格式化为标题 (如 "Type constraints")
            title = section['id'].replace('-', ' ').capitalize()
            if title == "Version":
                continue
            h3 = section.find('h3')
            if not h3:
                continue

            # 3. 提取 h3 之后的所有兄弟节点，确保内容不被截断
            content_parts = []
            for content_element in h3.find_next_siblings():
                # 使用换行符分隔，保持可读性
                content_parts.append(content_element.get_text(separator='\n', strip=True))

            content = '\n'.join(content_parts)

            if title and content:
                details[title] = content

        operator_data = {
            'name': op_name,
            'url': operator_url,
            'details': details
        }

        return operator_data

    except requests.exceptions.RequestException as e:
        print(f"Error fetching operator page {operator_url}: {e}")
        return None

def main():
    """
    主函数，执行整个爬取流程。
    """
    index_url = "https://onnx.ai/onnx/operators/index.html"
    print("Step 1: Fetching all operator links from the index page...")
    operator_links = get_operator_links(index_url)

    if not operator_links:
        print("Could not find any operator links. Exiting.")
        return

    print(f"Found {len(operator_links)} unique operator links.")

    all_operators_data = []
    print("\nStep 2: Scraping details for each operator...")
    for link in operator_links[:]:
        details = scrape_operator_details(link)
        if details:
            all_operators_data.append(details)
        time.sleep(0.5) # 礼貌性延迟，避免给服务器造成过大压力

    print("\nStep 3: Saving data to CSV and JSON files...")

    # 将列表转换为 DataFrame，方便保存
    df = pd.DataFrame(all_operators_data)

    # 保存为 CSV 文件
    df.to_csv('trainverify/onnx_operators.csv', index=False, encoding='utf-8-sig')
    print("Data saved to trainverify/onnx_operators.csv")

    # 保存为 JSON 文件
    # 使用 to_json 方法，orient='records' 表示保存为 [{column: value}, ...] 的格式
    df.to_json('trainverify/onnx_operators.json', orient='records', indent=4, force_ascii=False)
    print("Data saved to trainverify/onnx_operators.json")


if __name__ == '__main__':
    main()
